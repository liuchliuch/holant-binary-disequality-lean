import Holant.Certificates.FourthRootOdd.ExceptionalChecks
namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops

theorem exceptional_remaining (s : State) (hs : Exceptional s) : classify s=.remaining := by
  obtain ⟨e,he⟩ := hs.2
  simpa only [←he] using exceptional_parameter_remaining s.1 e hs.1

theorem exceptional_coefficient_relation (s : State) (hs : Exceptional s) :
    ∃ e : Bool, (∀ j : Fin 4, b s j=gmul (fourthRoot (signPhase e)) (a s j)) ∧
      (gmul (gmul (a s 0) (a s 1)) (gmul (a s 2) (a s 3))=(0,1) ∨
       gmul (gmul (a s 0) (a s 1)) (gmul (a s 2) (a s 3))=(0,-1)) := by
  obtain ⟨e,he⟩ := hs.2
  exact ⟨e,by simpa only [←he] using exceptional_parameter_coefficients s.1 e hs.1⟩

theorem exceptional_twoCopy_exact (s : State) (hs : Exceptional s) :
    ((Finset.univ : Finset (Fin 4 → Bool)).filter
      (fun x => exactTwoCopy s 0 x≠(0,0))).card=6 ∧
    exactTwoCopy s 0 (fun _ => false)≠(0,0) ∧ exactTwoCopy s 0 (fun _ => true)≠(0,0) := by
  obtain ⟨e,he⟩ := hs.2
  simpa only [←he] using exceptional_parameter_twoCopy s.1 e hs.1

theorem exceptional_twoCopy (s : State) (hs : Exceptional s) :
    ((Finset.univ : Finset (Fin 4 → Bool)).filter
      (fun x => twoCopyNative (complexOdd s) 0 x≠0)).card=6 ∧
    twoCopyNative (complexOdd s) 0 (fun _ => false)≠0 ∧
    twoCopyNative (complexOdd s) 0 (fun _ => true)≠0 := by
  classical
  simp_rw [twoCopyNative_eq,←embed_exactTwoCopy,ne_eq,embed_zero_iff]
  exact exceptional_twoCopy_exact s hs

end Holant.Certificates.FourthRootOdd
