import Holant.Certificates.FourthRootOdd.NormalizedTable
import Holant.Certificates.FourthRootOdd.ActualLoops
import Holant.Certificates.FourthRootOdd.Exceptional
import Holant.Certificates.FourthRootOdd.FamilyExit

/-! The complete normalized fourth-root odd interface of Theorem A.6.
Every asserted direct construction has an actual finite native-X network.
The analytic phase shift is kept separate from gadget availability. -/
noncomputable section
namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops Holant.Tractable

def RankOneExit (f : Signature ℂ 4) : Prop :=
  ∃ g : Signature ℂ 2,Gadget.Realizes (loopResources f) .disequality g ∧ (signatureMatrix g).rank=1
def InfiniteExit (f : Signature ℂ 4) : Prop :=
  ∃ g : Signature ℂ 2,Gadget.Realizes (loopResources f) .disequality g ∧
    IsUnit (signatureMatrix g*TwelveLoops.flip) ∧ ¬ProjectivelyFinite (signatureMatrix g*TwelveLoops.flip)
def SupportSixExit (f : Signature ℂ 4) : Prop :=
  Gadget.Realizes ({⟨4,f⟩} : SignatureFamily ℂ) .disequality (twoCopyNative f 0) ∧
    ((Finset.univ : Finset (Fin 4 → Bool)).filter (fun x => twoCopyNative f 0 x≠0)).card=6 ∧
    twoCopyNative f 0 (fun _ => false)≠0 ∧ twoCopyNative f 0 (fun _ => true)≠0 ∧
    ∀ x,evenWord x=false → twoCopyNative f 0 x=0
def NativeRankOrDense (f : Signature ℂ 4) : Prop :=
  (∃ e : Fin 6,Matrix.rank (fun x y : Bool => nativeContract f e ![x,y])=1 ∧
    Gadget.Realizes ({⟨4,f⟩} : SignatureFamily ℂ) .disequality (nativeContract f e)) ∨
  (∃ e : Fin 3,DenseProduct (twoCopyNative f (initialPair e)) ∧
    Gadget.Realizes ({⟨4,f⟩} : SignatureFamily ℂ) .disequality (twoCopyNative f (initialPair e)))
def PhaseExit (f : Signature ℂ 4) : Prop :=
  ∃ δ : Fin 4,∃ g : Signature AlgebraicComplex 4,
    Affine g ∧ (fun x => (g x : ℂ))=phaseShift f δ ∧ NativeRankOrDense (phaseShift f δ)

theorem exceptional_actual_exit (s : State) (h : Exceptional s) : SupportSixExit (complexOdd s) := by
  have hs := exceptional_twoCopy s h
  exact ⟨twoCopy_realizes _ _,hs.1,hs.2.1,hs.2.2,complexOdd_twoCopy_even s 0⟩

theorem remaining_actual_phase_exit (s : State) (hs : classify s=.remaining) (hn : ¬Exceptional s) :
    PhaseExit (complexOdd s) := by
  obtain ⟨δ,ha,he⟩ := remaining_shift_exit s hs hn
  refine ⟨δ,shiftedOdd s δ,ha,complexShiftedOdd_phaseShift s δ,?_⟩
  rw [←complexShiftedOdd_phaseShift s δ]
  exact he

/-- Source Theorem A.6 with the actual deterministic loop route preserved.
The first two exits use only the input table and the distinguished literal I;
the two-copy exits use exactly two copies of the stated input/shifted table. -/
theorem fourth_root_odd_contractions (f : Signature ℂ 4) (hf : NormalizedOdd f) :
    ∃ s : State,f=complexOdd s ∧
      (classify s=.rankOne → RankOneExit f) ∧
      (classify s=.infiniteOrder → InfiniteExit f) ∧
      (classify s=.remaining →
        (Exceptional s ∧ SupportSixExit f) ∨ (¬Exceptional s ∧ PhaseExit f)) := by
  obtain ⟨s,rfl⟩ := normalizedOdd_state f hf
  refine ⟨s,rfl,?_,?_,?_⟩
  · intro h
    obtain ⟨i,hr,hg⟩ := actual_rankOne_route s h
    exact ⟨loopOutput (complexOdd s) i,hg,hr⟩
  · intro h
    obtain ⟨i,hg,hu,hi⟩ := actual_infinite_route s h
    exact ⟨loopOutput (complexOdd s) i,hg,hu,hi⟩
  · intro h
    by_cases he : Exceptional s
    · exact Or.inl ⟨he,exceptional_actual_exit s he⟩
    · exact Or.inr ⟨he,remaining_actual_phase_exit s h he⟩

theorem fourth_root_odd_exit (f : Signature ℂ 4) (hf : NormalizedOdd f) :
    RankOneExit f ∨ InfiniteExit f ∨ SupportSixExit f ∨ PhaseExit f := by
  obtain ⟨s,hs,hr,hi,he⟩ := fourth_root_odd_contractions f hf
  cases hc : classify s with
  | rankOne => exact Or.inl (hr hc)
  | infiniteOrder => exact Or.inr (Or.inl (hi hc))
  | remaining =>
    rcases he hc with h | h
    · exact Or.inr (Or.inr (Or.inl h.2))
    · exact Or.inr (Or.inr (Or.inr h.2))

end Holant.Certificates.FourthRootOdd
