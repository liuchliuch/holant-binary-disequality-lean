import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionSupport
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionComponentsFull

/-! Close the structural split at the actual internally selected tensor.
The origin, XOR closure, parity alternative, and full-support alternative are
all derived from the original finite family's hypotheses. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionOrigin
open Holant Holant.Tractable GeneralEOPairedFamilyExtractionSupport
namespace E
export GeneralEOPairedFamilyExtractionChoice (compressed extracted extracted_closed extracted_failures)
end E
namespace T
export GeneralEOPairedFamilyExtractionTensor (tensor substitute)
end T
namespace C
export GeneralEOPairedFamilyExtractionComponentsFull (reduced reduced_full reduced_failures substitution expand_substitute)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ}

def paritySubstitution (u v : Fin n → Bool) : Fin n → Bool ⊕ Fin 3 := fun i =>
  if u i then (if v i then Sum.inr 2 else Sum.inr 0)
  else (if v i then Sum.inr 1 else Sum.inl false)

theorem parityWord_substitute (u v : Fin n → Bool) (z : Fin 3 → Bool) :
    parityWord u v z=T.substitute (paritySubstitution u v) z := by
  funext i
  cases hu : u i <;> cases hv : v i <;> simp [parityWord,T.substitute,paritySubstitution,hu,hv]

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))
variable (ha : ¬∀i,Affine (E.compressed G he hn hc i))
variable (hp : ¬∀i,Product (E.compressed G he hn hc i))

theorem extracted_origin : E.extracted G he hn hc ha hp origin≠0 := by
  change (E.compressed G he hn hc _) (fun _ => false)*
    (E.compressed G he hn hc _) (fun _ => false)≠0
  exact mul_ne_zero (compressed_origin_nonzero _ (he _) (hn _) (hc _))
    (compressed_origin_nonzero _ (he _) (hn _) (hc _))

theorem extracted_xorClosed : XorClosed (E.extracted G he hn hc ha hp) :=
  xorClosed_of_closed _ (extracted_origin G he hn hc ha hp) (E.extracted_closed G he hn hc ha hp)

/-- The first alternative is a real ternary parity minor; the second is a real
full-support minor retaining both class failures. No minor or support
partition is provided by the caller. -/
theorem structural_alternatives :
    (∃u v, (∀z,parityRow (E.extracted G he hn hc ha hp) u v z≠0 ↔
      Bool.xor (Bool.xor (z 0) (z 1)) (z 2)=false) ∧
      ¬Product (parityRow (E.extracted G he hn hc ha hp) u v)) ∨
    ((∀x,C.reduced (E.extracted G he hn hc ha hp) x≠0) ∧
      ¬Affine (C.reduced (E.extracted G he hn hc ha hp)) ∧
      ¬Product (C.reduced (E.extracted G he hn hc ha hp))) := by
  by_cases hm : MeetClosed (E.extracted G he hn hc ha hp)
  · exact Or.inr ⟨C.reduced_full _ (extracted_origin G he hn hc ha hp)
      (extracted_xorClosed G he hn hc ha hp) hm,
      C.reduced_failures _ (E.extracted_failures G he hn hc ha hp).1
        (E.extracted_failures G he hn hc ha hp).2⟩
  · obtain ⟨u,v,hu,hv,hs,hnp⟩ := exists_parity _ (extracted_origin G he hn hc ha hp)
      (extracted_xorClosed G he hn hc ha hp) hm
    exact Or.inl ⟨u,v,hs,hnp⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionOrigin
