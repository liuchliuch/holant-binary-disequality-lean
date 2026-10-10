import Holant.Proofs.Algorithms.TransformRecognition.PositiveWitnessSearch
import Holant.Proofs.Algorithms.TransformRecognition.EncodedGuard
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch.Search
import Mathlib.Data.Nat.Find


namespace Holant.LocalDrafts.MainChain.TransformRecognition.CertificateDovetail
open Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
variable {m k : ℕ}

/-- Each stage checks BOTH finite candidate families. Favoring a positive
return does not starve the negative search as the stage bound increases. -/
def stage (target : Fin m → RootCode) (S : EncodedSystem.System m (5+k))
    (height : ℕ) : Option Bool :=
  if (PositiveWitnessSearch.searchThrough target S height).isSome then some true
  else if (NullstellensatzSearch.searchThrough target S height).isSome then some false
  else none

theorem true_sound (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i))
    (S : EncodedSystem.System m (5+k)) (height : ℕ)
    (h : stage target S height = some true) :
    ∃ x : Fin (5+k) → ℂ, ∀ e ∈ S,
      MvPolynomial.aeval x (EncodedSystem.polynomial w e)=0 := by
  cases hp : PositiveWitnessSearch.searchThrough target S height with
  | some c =>
    obtain ⟨θ,_,hs,_⟩ := PositiveWitnessSearch.searchThrough_sound target w ht S height c hp
    exact ⟨_,hs⟩
  | none =>
    simp only [stage,hp,Option.isSome_none,Bool.false_eq_true,ite_false] at h
    split at h <;> simp at h

theorem false_sound (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i))
    (S : EncodedSystem.System m (5+k)) (height : ℕ)
    (h : stage target S height = some false) :
    ¬ ∃ x : Fin (5+k) → ℂ, ∀ e ∈ S,
      MvPolynomial.aeval x (EncodedSystem.polynomial w e)=0 := by
  cases hp : PositiveWitnessSearch.searchThrough target S height with
  | some c => simp [stage,hp] at h
  | none =>
    cases hn : NullstellensatzSearch.searchThrough target S height with
    | none => simp [stage,hp,hn] at h
    | some c => exact NullstellensatzSearch.searchThrough_sound target w ht S height c hn

theorem eventually_answer (w : Fin m → AlgebraicComplex) (target : Fin m → RootCode)
    (ht : ∀ i, (target i).Represents (w i : ℂ))
    (oneSlot negSlot : Fin m) (h₁ : w oneSlot = 1) (hneg : w negSlot = -1)
    (S : EncodedSystem.System m (5+k)) :
    ∃ height, ∀ h ≥ height,
      (stage target (EncodedGuard.augment oneSlot negSlot S) h).isSome = true := by
  classical
  let T := EncodedGuard.augment oneSlot negSlot S
  by_cases hn : NullstellensatzSearch.NoAlgebraicSolution w T
  · obtain ⟨height,hh⟩ := NullstellensatzSearch.eventually_some w target ht T hn
    refine ⟨height,fun h hh' => ?_⟩
    have he := hh h hh'
    change (stage target T h).isSome = true
    by_cases hp : (PositiveWitnessSearch.searchThrough target T h).isSome = true
    · simp only [stage,hp,ite_true,Option.isSome_some]
    · simp only [stage,hp,Bool.false_eq_true,ite_false,he,ite_true,Option.isSome_some]
  · obtain ⟨y,hy⟩ : ∃ y : Fin (5+k) → AlgebraicComplex, ∀ e ∈ T,
        MvPolynomial.aeval y (NullstellensatzSearch.equation w e)=0 :=
      Classical.not_not.mp hn
    have hg := EncodedGuard.of_system w oneSlot negSlot h₁ hneg S y hy
    have hyC : ∀ e ∈ T, MvPolynomial.aeval (fun j => (y j : ℂ))
        (EncodedSystem.polynomial (fun i => (w i : ℂ)) e)=0 := by
      intro e he
      rw [NullstellensatzSearch.eval_equation_coe,hy e he]
      rfl
    obtain ⟨height,hh⟩ := PositiveWitnessSearch.eventually_some w target ht T y hyC hg
    refine ⟨height,fun h hh' => ?_⟩
    obtain ⟨c,hc⟩ := hh h hh'
    change (stage target T h).isSome = true
    simp only [stage,hc,Option.isSome_some,ite_true]

/-- Faithfulness of the input coefficient codes, with two literal constant
slots. This is not a witness for the polynomial-system decision problem. -/
def Valid (target : Fin m → RootCode) (oneSlot negSlot : Fin m) : Prop :=
  ∃ w : Fin m → AlgebraicComplex,
    (∀ i, (target i).Represents (w i : ℂ)) ∧ w oneSlot=1 ∧ w negSlot=-1

theorem terminates (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : Valid target oneSlot negSlot) :
    ∃ height, (stage target (EncodedGuard.augment oneSlot negSlot S) height).isSome=true := by
  obtain ⟨w,ht,h₁,hneg⟩ := hv
  obtain ⟨height,hh⟩ := eventually_answer w target ht oneSlot negSlot h₁ hneg S
  exact ⟨height,hh height le_rfl⟩

/-- Nat.find executes increasing finite stages using their COMPUTABLE Bool
test. The proof of termination is erased; no Classical.choose selects an
answer or a semantic root at runtime. No uniform polynomial bound is claimed. -/
def answer (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : Valid target oneSlot negSlot) : Bool :=
  (stage target (EncodedGuard.augment oneSlot negSlot S)
    (Nat.find (terminates target oneSlot negSlot S hv))).getD false

theorem answer_stage (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : Valid target oneSlot negSlot) :
    stage target (EncodedGuard.augment oneSlot negSlot S)
      (Nat.find (terminates target oneSlot negSlot S hv)) =
        some (answer target oneSlot negSlot S hv) := by
  have hs := Nat.find_spec (terminates target oneSlot negSlot S hv)
  generalize he : stage target (EncodedGuard.augment oneSlot negSlot S)
    (Nat.find (terminates target oneSlot negSlot S hv)) = result at hs
  cases result with
  | none => simp at hs
  | some b => simpa only [answer,he,Option.getD_some] using he

theorem answer_correct (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i)) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : Valid target oneSlot negSlot) :
    answer target oneSlot negSlot S hv = true ↔
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

end Holant.LocalDrafts.MainChain.TransformRecognition.CertificateDovetail
