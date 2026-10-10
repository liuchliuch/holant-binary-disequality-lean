import Holant.Proofs.Algorithms.TransformRecognition.StructuredCatalogue
import Holant.Proofs.Algorithms.TransformRecognition.CertificateDovetail


namespace Holant.LocalDrafts.MainChain.TransformRecognition.StructuredDovetail
open Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
variable {m k : ℕ}

def positive (target : Fin m → RootCode) (S : EncodedSystem.System m (5+k)) (h : ℕ) : Bool :=
  (StructuredCatalogue.positive m k h).any (PositiveWitnessSearch.check target S)
def negative (target : Fin m → RootCode) (S : EncodedSystem.System m (5+k)) (h : ℕ) : Bool :=
  (StructuredCatalogue.negative m (5+k) S.length h).any (NullstellensatzSearch.check target S)
def stage (target : Fin m → RootCode) (S : EncodedSystem.System m (5+k)) (h : ℕ) : Option Bool :=
  if positive target S h then some true else if negative target S h then some false else none

theorem positive_sound (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i)) (S : EncodedSystem.System m (5+k)) (h : ℕ)
    (hc : positive target S h=true) :
    ∃ x : Fin (5+k) → ℂ, ∀ e ∈ S, MvPolynomial.aeval x (EncodedSystem.polynomial w e)=0 := by
  obtain ⟨c,_,hc⟩ := List.any_eq_true.mp hc
  obtain ⟨θ,_,he,_⟩ := PositiveWitnessSearch.checked_sound target w ht S c hc
  exact ⟨_,he⟩

theorem negative_sound (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i)) (S : EncodedSystem.System m (5+k)) (h : ℕ)
    (hc : negative target S h=true) :
    ¬ ∃ x : Fin (5+k) → ℂ, ∀ e ∈ S, MvPolynomial.aeval x (EncodedSystem.polynomial w e)=0 := by
  obtain ⟨c,_,hc⟩ := List.any_eq_true.mp hc
  exact NullstellensatzSearch.check_sound target w ht S c hc

theorem true_sound (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i)) (S : EncodedSystem.System m (5+k)) (h : ℕ)
    (hc : stage target S h=some true) :
    ∃ x : Fin (5+k) → ℂ, ∀ e ∈ S, MvPolynomial.aeval x (EncodedSystem.polynomial w e)=0 := by
  by_cases hp : positive target S h=true
  · exact positive_sound target w ht S h hp
  · by_cases hn : negative target S h=true <;> simp [stage,hp,hn] at hc

theorem false_sound (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i)) (S : EncodedSystem.System m (5+k)) (h : ℕ)
    (hc : stage target S h=some false) :
    ¬ ∃ x : Fin (5+k) → ℂ, ∀ e ∈ S, MvPolynomial.aeval x (EncodedSystem.polynomial w e)=0 := by
  by_cases hp : positive target S h=true
  · simp [stage,hp] at hc
  · by_cases hn : negative target S h=true
    · exact negative_sound target w ht S h hn
    · simp [stage,hp,hn] at hc

/-- Any checked witness persists in the structural catalogue at every large
enough height. Earlier Encodable stage indices are never treated as bit sizes. -/
theorem eventually_of_checked (target : Fin m → RootCode) (S : EncodedSystem.System m (5+k))
    (hc : (∃ c, PositiveWitnessSearch.check target S c=true) ∨
      ∃ c, NullstellensatzSearch.check target S c=true) :
    ∃ H, ∀ h ≥ H, (stage target S h).isSome=true := by
  rcases hc with ⟨c,hc⟩ | ⟨c,hc⟩
  · obtain ⟨H,hH⟩ := StructuredCatalogue.covers_positive m k c
    refine ⟨H,fun h hh => ?_⟩
    have hp : positive target S h=true := List.any_eq_true.mpr ⟨c,hH h hh,hc⟩
    simp [stage,hp]
  · obtain ⟨H,hH⟩ := StructuredCatalogue.covers_negative m (5+k) S.length c
    refine ⟨H,fun h hh => ?_⟩
    have hn : negative target S h=true := List.any_eq_true.mpr ⟨c,hH h hh,hc⟩
    simp only [stage,hn,ite_true]
    split <;> rfl

theorem checked_exists (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    (∃ c, PositiveWitnessSearch.check target (EncodedGuard.augment oneSlot negSlot S) c=true) ∨
      ∃ c, NullstellensatzSearch.check target (EncodedGuard.augment oneSlot negSlot S) c=true := by
  obtain ⟨h,hh⟩ := CertificateDovetail.terminates target oneSlot negSlot S hv
  cases hp : PositiveWitnessSearch.searchThrough target (EncodedGuard.augment oneSlot negSlot S) h with
  | some c =>
    exact Or.inl ⟨c,PositiveWitnessSearch.first_checked target _ _ c hp⟩
  | none =>
    cases hn : NullstellensatzSearch.searchThrough target (EncodedGuard.augment oneSlot negSlot S) h with
    | none => simp [CertificateDovetail.stage,hp,hn] at hh
    | some c =>
      right
      refine ⟨c,?_⟩
      exact NullstellensatzSearch.searchThrough_checked target _ h c hn

theorem terminates (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    ∃ h, (stage target (EncodedGuard.augment oneSlot negSlot S) h).isSome=true := by
  obtain ⟨H,hH⟩ := eventually_of_checked target _ (checked_exists target oneSlot negSlot S hv)
  exact ⟨H,hH H le_rfl⟩

def answer (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) : Bool :=
  (stage target (EncodedGuard.augment oneSlot negSlot S)
    (Nat.find (terminates target oneSlot negSlot S hv))).getD false

theorem answer_stage (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    stage target (EncodedGuard.augment oneSlot negSlot S)
      (Nat.find (terminates target oneSlot negSlot S hv))=some (answer target oneSlot negSlot S hv) := by
  have hs := Nat.find_spec (terminates target oneSlot negSlot S hv)
  generalize he : stage target (EncodedGuard.augment oneSlot negSlot S)
    (Nat.find (terminates target oneSlot negSlot S hv))=result at hs
  cases result with
  | none => simp at hs
  | some b => simpa only [answer,he,Option.getD_some] using he

theorem answer_correct (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i)) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    answer target oneSlot negSlot S hv=true ↔
    ∃ x : Fin (5+k) → ℂ, ∀ e ∈ EncodedGuard.augment oneSlot negSlot S,
      MvPolynomial.aeval x (EncodedSystem.polynomial w e)=0 := by
  have hs := answer_stage target oneSlot negSlot S hv
  cases ha : answer target oneSlot negSlot S hv with
  | true =>
    rw [ha] at hs
    exact iff_of_true rfl (true_sound target w ht _ _ hs)
  | false =>
    rw [ha] at hs
    exact iff_of_false Bool.false_ne_true (false_sound target w ht _ _ hs)

theorem answer_eq_legacy (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    answer target oneSlot negSlot S hv=CertificateDovetail.answer target oneSlot negSlot S hv := by
  have hvalid := hv
  obtain ⟨w,hw,_,_⟩ := hvalid
  have h := (answer_correct target (fun i => (w i : ℂ)) hw oneSlot negSlot S hv).trans
    (CertificateDovetail.answer_correct target _ hw oneSlot negSlot S hv).symm
  exact Bool.eq_iff_iff.mpr h

end Holant.LocalDrafts.MainChain.TransformRecognition.StructuredDovetail
