import Holant.Platonic.StabilizerErasure.PauliBasis

/-! The KL basis consists of actual physical Paulis supported at the chosen
port.  This connects the finite two-by-two matrices to Clifford compression. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.ReedMuller.RadonAccess Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

def physicalPauli (r : Fin (n+1)) : Fin 4 → Pauli (n+1)
  | 0 => ⟨0,0,0⟩
  | 1 => ⟨0,unitWord r,0⟩
  | 2 => ⟨3,unitWord r,LinearMap.proj r⟩
  | 3 => ⟨0,0,LinearMap.proj r⟩

theorem wordVector_add_unit (r : Fin (n+1)) (w : Word (n+1)) :
    wordVector (vectorWord w+unitWord r)=Function.update w r (!(w r)) := by
  ext j
  by_cases hj : j=r
  · subst j
    cases h : w r <;> simp [wordVector,vectorWord,unitWord_apply,boolEquiv,h]
  · simp [wordVector,vectorWord,unitWord_apply,hj]

theorem physicalPauli_exact (r : Fin (n+1)) (p : Fin 4) (f : Signature ℂ (n+1)) :
    (physicalPauli r p).run f=siteAction r (qubitPauli p) f := by
  ext w
  fin_cases p <;> cases hw : w r <;>
    simp [physicalPauli,Pauli.run,siteAction,qubitPauli,wordVector_add_unit,
      vectorWord,boolEquiv,hw,phaseRoot,Holant.Tractable.fourthRootPhase]
  all_goals norm_num [show (3 : ZMod 4).val=3 by decide,pow_succ,Complex.I_mul_I]

theorem physicalPauli_involution (r : Fin (n+1)) (p : Fin 4) (f : Signature ℂ (n+1)) :
    (physicalPauli r p).run ((physicalPauli r p).run f)=f := by
  simp only [physicalPauli_exact]
  exact siteAction_qubitPauli_involution r p f

theorem correctable_pauli_scalar_values (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) (h : Correctable V r) (p : Fin 4) :
    ∃c : ℂ,(c=0 ∨ c=1 ∨ c= -1) ∧
      ∀f,V.adjoint (siteAction r (qubitPauli p) (V.map f))=c • f := by
  obtain ⟨c,hc⟩ := h (qubitPauli p)
  refine ⟨c,?_,hc⟩
  apply V.scalar_involution_values (physicalPauli r p) (physicalPauli_involution r p) c
  simpa only [physicalPauli_exact] using hc

/-- Failure of single-site erasure gives a nontrivial logical Pauli with an
actual physical representative on that port alone, as used in the source's
column-normal-form argument. -/
theorem not_correctable_logical_representative (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) (h : ¬Correctable V r) :
    ∃p : Fin 4,∃Q : Pauli k,p≠0 ∧ (Q.shift≠0 ∨ Q.character≠0) ∧
      ∀f,siteAction r (qubitPauli p) (V.map f)=V.map (Q.run f) := by
  obtain ⟨p,hp,hn⟩ := not_correctable_pauli V r h
  obtain ⟨Q,hQ,he⟩ := V.nonscalar_pauli_lift (physicalPauli r p)
    (by simpa only [physicalPauli_exact] using hn)
  exact ⟨p,Q,hp,hQ,by simpa only [physicalPauli_exact] using he⟩

end
end Holant.Platonic.StabilizerErasure
