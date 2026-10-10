import Holant.Certificates.FourthRootOdd.Source

/-! Finite sets for the two exact odd-coset shift classes. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

def oddPhaseStates (δ : Fin 4) : Finset State :=
  Finset.univ.filter (fun s => classify s=.remaining ∧ ¬Exceptional s ∧ phaseTest s δ)

def oddRemainingStates : Finset State :=
  Finset.univ.filter (fun s => classify s=.remaining ∧ ¬Exceptional s)

def oddFamilyPreimage (δ : Fin 4) (p : FamilyParameters) : State :=
  shiftState (familyState p) (-δ)

def oddPhaseParameters (δ : Fin 4) : Finset FamilyParameters :=
  Finset.univ.filter (fun p => classify (oddFamilyPreimage δ p)=.remaining ∧
    ¬Exceptional (oddFamilyPreimage δ p))

theorem shiftState_zero (s : State) : shiftState s 0=s := by
  rcases s with ⟨a,b,c,d,e⟩
  simp [shiftState]

theorem shiftState_add (s : State) (δ ε : Fin 4) :
    shiftState (shiftState s δ) ε=shiftState s (δ+ε) := by
  rcases s with ⟨a,b,c,d,e⟩
  simp [shiftState,add_assoc]

theorem shiftState_neg (s : State) (δ : Fin 4) : shiftState (shiftState s δ) (-δ)=s := by
  rw [shiftState_add,add_neg_cancel,shiftState_zero]

theorem shiftState_injective (δ : Fin 4) : Function.Injective (fun s => shiftState s δ) := by
  intro s t h
  have he := congrArg (fun u => shiftState u (-δ)) h
  simpa only [shiftState_neg] using he

theorem oddFamilyPreimage_injective (δ : Fin 4) : Function.Injective (oddFamilyPreimage δ) :=
  (shiftState_injective (-δ)).comp familyState_injective

theorem oddFamilyPreimage_phase (δ : Fin 4) (p : FamilyParameters) :
    phaseTest (oddFamilyPreimage δ p) δ := by
  apply (phaseTest_shift _ _).mp
  simpa only [oddFamilyPreimage,shiftState_add,neg_add_cancel,shiftState_zero] using family_phase_test p

theorem phaseTest_preimage (s : State) (δ : Fin 4) (h : phaseTest s δ) :
    ∃ p,s=oddFamilyPreimage δ p := by
  refine ⟨recoverFamily (shiftState s δ) 0,?_⟩
  have hh := phase_test_in_family (shiftState s δ) ((phaseTest_shift s δ).mpr h)
  rw [oddFamilyPreimage,←hh,shiftState_neg]

theorem oddPhaseStates_image (δ : Fin 4) :
    oddPhaseStates δ=(oddPhaseParameters δ).image (oddFamilyPreimage δ) := by
  ext s
  simp only [oddPhaseStates,oddPhaseParameters,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · rintro ⟨hr,hn,hp⟩
    obtain ⟨p,rfl⟩ := phaseTest_preimage s δ hp
    exact ⟨p,⟨hr,hn⟩,rfl⟩
  · rintro ⟨p,⟨hr,hn⟩,rfl⟩
    exact ⟨hr,hn,oddFamilyPreimage_phase δ p⟩

theorem oddPhaseStates_card (δ : Fin 4) :
    (oddPhaseStates δ).card=(oddPhaseParameters δ).card := by
  rw [oddPhaseStates_image,Finset.card_image_of_injective _ (oddFamilyPreimage_injective δ)]

end Holant.Certificates.AffineEndpointCounts
