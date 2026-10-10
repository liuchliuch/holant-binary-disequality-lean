import Holant.Platonic.RankDeficientLocalization.DomainSemantics
import Holant.Certificates.MatchingProductBridge.ConeEmbedding

/-! The three residual matching labels are recovered from literal four-port
presentations, so later normalization never assumes a preassigned colouring. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit
open Holant.Certificates.MatchingContractionClosure
open Holant.Platonic.RainbowLocalization
noncomputable section
set_option backward.isDefEq.respectTransparency false

def fourPorts (r : Fin 3) : (Fin 2 × Bool) ≃ Fin 4 where
  toFun := fun (e,b) =>
    (![![![0,1],![2,3]],![![0,2],![1,3]],![![0,3],![1,2]]] r e) (if b then 1 else 0)
  invFun := fun j => ![![(0,false),(0,true),(1,false),(1,true)],
    ![(0,false),(1,false),(0,true),(1,true)],
    ![(0,false),(1,false),(1,true),(0,true)]] r j
  left_inv := by fin_cases r <;> decide
  right_inv := by fin_cases r <;> decide

def fourPresentation (r : Fin 3) (U V : Matrix Bool Bool ℂ) : Presentation ℂ (Fin 4) where
  edges := 2
  ports := fourPorts r
  matrix := ![U,V]
  scalar := 1

theorem fourPresentation_tensor (r : Fin 3) (U V : Matrix Bool Bool ℂ) :
    (fourPresentation r U V).tensor=matchingTensor r U V := by
  funext x
  change (1 : ℂ)*(∏e : Fin 2,(![U,V] e) (x (fourPorts r (e,false))) (x (fourPorts r (e,true))))=_
  rw [one_mul,Fin.prod_univ_two]
  fin_cases r <;> rfl

def fourCard (r : Fin 3) (U V : Matrix Bool Bool ℂ) (hU : U.det≠0) (hV : V.det≠0) :
    NonsingularCard (matchingTensor r U V) where
  presentation := fourPresentation r U V
  det_ne_zero := by intro e; fin_cases e <;> assumption
  scalar_ne_zero := one_ne_zero
  value := (fourPresentation_tensor r U V).symm

def fourMatching (r : Fin 3) : Equiv.Perm (Fin 4) :=
  (presentationMatching (fourPresentation r 1 1)).mate

theorem fourCard_matching (r : Fin 3) (U V : Matrix Bool Bool ℂ)
    (hU : U.det≠0) (hV : V.det≠0) : (fourCard r U V hU hV).matching=fourMatching r := rfl

theorem fourMatching_injective : Function.Injective fourMatching := by
  intro r s he
  have hh := congrArg (fun e : Equiv.Perm (Fin 4) => e 0) he
  have hv : ∀t : Fin 3, fourMatching t 0=(![1,2,3] : Fin 3 → Fin 4) t := by
    intro t
    fin_cases t <;> rfl
  rw [hv,hv] at hh
  exact (show Function.Injective (![1,2,3] : Fin 3 → Fin 4) from by decide) hh

theorem matchingCone_card (g : PlatonicModel) (F : FourTensor) (hF : matchingCone g F) :
    F=0 ∨ Nonempty (NonsingularCard F) := by
  rcases matchingCone_presentation g F hF with hz | ⟨r,U,V,hU,hV,rfl⟩
  · exact Or.inl hz
  · exact Or.inr ⟨fourCard r U V (groupDirection_det_ne_zero g hU) (groupDirection_det_ne_zero g hV)⟩

theorem card_matching_of_tensor {F : FourTensor} (D : NonsingularCard F)
    {r : Fin 3} {U V : Matrix Bool Bool ℂ} (hU : U.det≠0) (hV : V.det≠0)
    (he : F=matchingTensor r U V) : D.matching=fourMatching r := by
  subst F
  exact D.matching_eq (fourCard r U V hU hV)

end
end Holant.Platonic.RankDeficientLocalization.Normalization
