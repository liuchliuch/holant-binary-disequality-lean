import Holant.Certificates.AffineReference.FullEvenSemantics
import Holant.Certificates.FourthRootOdd.PhaseWitness
import Holant.Certificates.AffineEndpoint.ReferenceCoverage

/-! Duplicate-free enumeration of the actual normalized full-even affine
references. Neither support nor membership in Affine is assumed of the list. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.Certificates.TwelveLoops
open Holant.Certificates.FourthRootOdd Holant.Certificates.AffineReference
set_option backward.isDefEq.respectTransparency false

def evenSystem : AffineSystem 4 := ⟨1,fun _ _ => 1,fun _ => 0⟩
theorem evenSystem_holds : ∀ x : Fin 4 → Bool,evenSystem.Holds x ↔ evenWord x=true := by decide +kernel

def evenChartPhase (p : EvenParameters) (y : Fin 3 → Bool) : ZMod 4 :=
  AffineReference.phaseCode (evenPhase p (evenChart y))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
theorem evenChartPhase_criterion : ∀ p : EvenParameters,PhaseCriterion (evenChartPhase p) := by decide +kernel

noncomputable section

theorem evenAlg_affine (p : EvenParameters) : Affine (evenAlg p) := by
  have ha := affine_formula 1 evenSystem
    (phaseQuadratic (evenChartPhase p) (evenChartPhase_criterion p))
  convert ha using 1
  funext x
  simp only [affineFormula,evenSystem_holds,evenAlg]
  split_ifs with hx
  · rw [phaseQuadratic_eval,phasePoly3_eq _ (evenChartPhase_criterion p)]
    simp only [one_mul,evenChartPhase,evenChart_original x hx]
  · rfl

theorem evenAlg_origin (p : EvenParameters) : evenAlg p (fun _ => false)=1 := by
  simp [evenAlg,evenPhase,phaseBit,evenWord,AffineReference.phaseCode]

theorem evenAlg_support (p : EvenParameters) (x : Fin 4 → Bool) :
    evenAlg p x≠0 ↔ evenWord x=true := by
  simp [evenAlg,Holant.Tractable.fourthRootPhase_ne_zero]

end

def rootCode (z : Gaussian) : Fin 4 :=
  if z=(1,0) then 0 else if z=(0,1) then 1 else if z=(-1,0) then 2 else 3

def recoverEven (q : Signature Gaussian 4) : EvenParameters :=
  let a := rootCode (q (evenChart ![true,false,false]))
  let b := rootCode (q (evenChart ![false,true,false]))
  let c := rootCode (q (evenChart ![false,false,true]))
  ((a,b,c),decide (rootCode (q (evenChart ![true,true,false]))-a-b=2),
    decide (rootCode (q (evenChart ![true,false,true]))-a-c=2),
    decide (rootCode (q (evenChart ![false,true,true]))-b-c=2))

set_option maxRecDepth 200000 in
theorem recoverEven_evenTable : ∀ p : EvenParameters,recoverEven (evenTable p)=p := by decide +kernel

theorem evenTable_injective : Function.Injective evenTable := by
  intro p q h
  simpa only [recoverEven_evenTable] using congrArg recoverEven h

noncomputable section

theorem algEmbed_injective : Function.Injective algEmbed := by
  intro z w h
  have he : embed z=embed w := by simpa using congrArg (fun a : AlgebraicComplex => (a : ℂ)) h
  apply Prod.ext
  · have hr := congrArg Complex.re he
    simpa [embed] using hr
  · have hi := congrArg Complex.im he
    simpa [embed] using hi

theorem evenAlg_injective : Function.Injective evenAlg := by
  intro p q h
  apply evenTable_injective
  funext x
  apply algEmbed_injective
  simpa only [algEmbed_evenTable] using congrFun h x

/-- The actual source family, expressed without a finite-code premise. -/
def fullEvenReferences : Set (Signature AlgebraicComplex 4) :=
  {h | Affine h ∧ h (fun _ => false)=1 ∧ ∀ x,h x≠0 ↔ evenWord x=true}

theorem fullEvenReferences_eq_range : fullEvenReferences=Set.range evenAlg := by
  ext h
  constructor
  · rintro ⟨ha,h0,hs⟩
    obtain ⟨p,hp⟩ := full_even_coverage h ha hs h0
    exact ⟨p,hp.symm⟩
  · rintro ⟨p,rfl⟩
    exact ⟨evenAlg_affine p,evenAlg_origin p,evenAlg_support p⟩

theorem full_even_actual_count : fullEvenReferences.ncard=512 := by
  rw [fullEvenReferences_eq_range,Set.ncard_range_of_injective evenAlg_injective,Nat.card_eq_fintype_card]
  exact full_even_parameter_count

theorem full_even_is_actual_reference (p : EvenParameters) :
    ∃ r : Fin 612,evenAlg p=AffineEndpoint.reference r :=
  AffineEndpoint.reference_coverage _ (evenAlg_affine p) (evenAlg_origin p)
    (Or.inr (Or.inr (evenAlg_support p)))

end
end Holant.Certificates.AffineEndpointCounts
