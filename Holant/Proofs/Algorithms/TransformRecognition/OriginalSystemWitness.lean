import Holant.Proofs.Algorithms.TransformRecognition.OriginalSystemDecision
import Holant.Proofs.Algorithms.TransformRecognition.StructuredWitness


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalSystemWitness
open Holant Holant.Tractable MvPolynomial
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open PowerArithmetic Sparse
variable {m q : ℕ}

structure Result (d q : ℕ) where
  witness : StructuredWitness.Output d q
  «variables» : Fin (5+q) → PowerArithmetic.Vector d

def emit {r : ℕ} (c : PositiveWitnessSearch.Candidate r q) : Result c.1.1 q :=
  ⟨StructuredWitness.emit c,c.1.2.2.2.2⟩

abbrev Candidate (S : List (Poly (5+q) 1)) :=
  PositiveWitnessSearch.Candidate (m+RationalInputSystem.count S) q

def candidate (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (S : List (Poly (5+q) 1)) (address : Fin m → Fin (5+q)) : Option (Candidate (m:=m) S) :=
  StructuredWitness.candidate (RationalInputSystem.target input S)
    (OriginalSystemDecision.oneSlot S) (OriginalSystemDecision.negSlot S)
    (RationalInputSystem.system S address) (OriginalSystemDecision.target_valid input hv S)

def output (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (S : List (Poly (5+q) 1)) (address : Fin m → Fin (5+q)) : Option (Σ d, Result d q) :=
  (candidate input hv S address).map (fun c => ⟨c.1.1,emit c⟩)

theorem candidate_isSome (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (S : List (Poly (5+q) 1)) (address : Fin m → Fin (5+q)) :
    (candidate input hv S address).isSome=true ↔
      OriginalSystemDecision.answer input hv S address=true :=
  StructuredWitness.candidate_isSome _ _ _ _ _

theorem output_isSome (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (S : List (Poly (5+q) 1)) (address : Fin m → Fin (5+q)) :
    (output input hv S address).isSome=true ↔
      OriginalSystemDecision.answer input hv S address=true := by
  simpa only [output,Option.isSome_map] using candidate_isSome input hv S address

/-- Correctness of the literal returned values. The original coefficients
retain their specified conjugates, including when several RootCodes share a
polynomial. The relation need not be irreducible. -/
theorem emitted_candidate_sound (input : Fin m → RootCode)
    (hv : OriginalSystemDecision.Valid input) (w : Fin m → AlgebraicComplex)
    (hw : ∀ i, (input i).Represents (w i : ℂ))
    (S : List (Poly (5+q) 1)) (address : Fin m → Fin (5+q))
    (c : Candidate (m:=m) S) (hc : candidate input hv S address=some c) :
    ∃ θ : AlgebraicComplex,
      (emit c).witness.root.Represents (θ : ℂ) ∧
      θ^(c.1.1+1)=decode θ (emit c).witness.relation ∧
      (Kernel.mul (fun u v => decode θ ((emit c).witness.coordinates.matrix u v))
        (fun u v => decode θ ((emit c).witness.coordinates.inverse u v))=Signature.equality ∧
       Kernel.mul (fun u v => decode θ ((emit c).witness.coordinates.inverse u v))
        (fun u v => decode θ ((emit c).witness.coordinates.matrix u v))=Signature.equality) ∧
      (∀ i, (decode θ ((emit c).variables (address i)) : ℂ)=(w i : ℂ)) ∧
      ∀ p ∈ S, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ)
        (fun i => (decode θ ((emit c).variables i) : ℂ)) p=0 := by
  have hcheck := StructuredWitness.candidate_sound (RationalInputSystem.target input S)
    (OriginalSystemDecision.oneSlot S) (OriginalSystemDecision.negSlot S)
    (RationalInputSystem.system S address) (OriginalSystemDecision.target_valid input hv S) c hc
  obtain ⟨θ,hroot,hrel,hinv,hzero⟩ := StructuredWitness.emit_sound
    (RationalInputSystem.target input S) (OriginalSystemDecision.values w S)
    (OriginalSystemDecision.target_represents input w hw S)
    (EncodedGuard.augment (OriginalSystemDecision.oneSlot S) (OriginalSystemDecision.negSlot S)
      (RationalInputSystem.system S address)) c hcheck
  have hsys : ∀ e ∈ RationalInputSystem.system S address,
      aeval (fun i => (decode θ (c.1.2.2.2.2 i) : ℂ))
        (EncodedSystem.polynomial (RationalInputSystem.values (fun i => (w i : ℂ)) S) e)=0 := by
    intro e he
    have hh := hzero e (List.mem_cons_of_mem _ he)
    rw [OriginalSystemDecision.values_coe] at hh
    exact hh
  obtain ⟨hb,he⟩ := (RationalInputSystem.system_zero_iff
    (fun i => (w i : ℂ)) S address (fun i => (decode θ (c.1.2.2.2.2 i) : ℂ))).mp hsys
  exact ⟨θ,hroot,hrel,hinv,hb,he⟩

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalSystemWitness
