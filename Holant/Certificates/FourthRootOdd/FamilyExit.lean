import Holant.Certificates.FourthRootOdd.DenseCertificate
import Holant.Certificates.FourthRootOdd.DenseSemantics
import Holant.Certificates.FourthRootOdd.TwoCopyNetwork
import Holant.Certificates.FourthRootOdd.NativeLoop
import Holant.Certificates.FourthRootOdd.FamilyDispatch
import Holant.Certificates.FourthRootOdd.PhaseDispatch

namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops Holant.Tractable

theorem complexOdd_native_matrix (s : State) (p : Fin 6) :
    (fun x y : Bool => nativeContract (complexOdd s) p ![x,y])=
      transfer (nativePair s p).1 (nativePair s p).2 := by
  exact native_loop_matrix s p

theorem family_rank_or_dense (p : FamilyParameters) :
    (∃ e : Fin 6,
      Matrix.rank (fun x y : Bool => nativeContract (complexOdd (familyState p)) e ![x,y])=1 ∧
      Gadget.Realizes ({⟨4,complexOdd (familyState p)⟩} : SignatureFamily ℂ) .disequality
        (nativeContract (complexOdd (familyState p)) e)) ∨
    (∃ e : Fin 3, DenseProduct (twoCopyNative (complexOdd (familyState p)) (initialPair e)) ∧
      Gadget.Realizes ({⟨4,complexOdd (familyState p)⟩} : SignatureFamily ℂ) .disequality
        (twoCopyNative (complexOdd (familyState p)) (initialPair e))) := by
  have hw := family_witness_correct p
  cases h : printedFamilyWitness p with
  | inl e =>
    rw [h] at hw
    left
    refine ⟨e,?_,nativeContract_realizes _ _⟩
    rw [complexOdd_native_matrix]
    exact (rankOneTest_rank _ _ hw).1
  | inr w =>
    rw [h] at hw
    rcases w with ⟨e,u,m⟩
    exact Or.inr ⟨e,dense_output_of_certificate p e u m hw,twoCopy_realizes _ _⟩

theorem coe_phase_root (k : Fin 4) :
    ((fourthRootPhase (k.val : ZMod 4) : AlgebraicComplex) : ℂ)=embed (fourthRoot k) := by
  fin_cases k <;> norm_num [fourthRoot,embed]

noncomputable def complexShiftedOdd (s : State) (δ : Fin 4) : Signature ℂ 4 :=
  fun x => (shiftedOdd s δ x : ℂ)

/-- The source phase operation on the actual input coefficients. It is an
analytic table operation, not a claim that a phase gadget is freely supplied. -/
def phaseShift (f : Signature ℂ 4) (δ : Fin 4) : Signature ℂ 4 :=
  oddTable (fun j => f (singleWord j))
    (fun j => embed (fourthRoot δ)*f (complementWord j))

theorem complexShiftedOdd_phaseShift (s : State) (δ : Fin 4) :
    complexShiftedOdd s δ=phaseShift (complexOdd s) δ := by
  have ht : phaseShift (complexOdd s) δ=oddTable (fun j => embed (a s j))
      (fun j => embed (fourthRoot δ)*embed (b s j)) := by
    simp only [phaseShift,complexOdd,oddTable_single,oddTable_complement]
  rw [ht]
  funext x
  unfold complexShiftedOdd
  rw [shiftedOdd_table]
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> cases h₃ : x 3 <;>
    simp [oddTable,
      h₀,h₁,h₂,h₃,a,b,fourthRootPhase_add,coe_phase_root,mul_comm]

theorem complexShiftedOdd_zero (s : State) : complexShiftedOdd s 0=complexOdd s := by
  funext x
  unfold complexShiftedOdd
  rw [shiftedOdd_table]
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> cases h₃ : x 3 <;>
    simp [complexOdd,oddTable,h₀,h₁,h₂,h₃,a,b,coe_phase_root]

theorem remaining_shift_exit (s : State) (hs : classify s=.remaining) (hn : ¬Exceptional s) :
    ∃ δ : Fin 4, Affine (shiftedOdd s δ) ∧
      ((∃ e : Fin 6,
        Matrix.rank (fun x y : Bool => nativeContract (complexShiftedOdd s δ) e ![x,y])=1 ∧
        Gadget.Realizes ({⟨4,complexShiftedOdd s δ⟩} : SignatureFamily ℂ) .disequality
          (nativeContract (complexShiftedOdd s δ) e)) ∨
      (∃ e : Fin 3, DenseProduct (twoCopyNative (complexShiftedOdd s δ) (initialPair e)) ∧
        Gadget.Realizes ({⟨4,complexShiftedOdd s δ⟩} : SignatureFamily ℂ) .disequality
          (twoCopyNative (complexShiftedOdd s δ) (initialPair e)))) := by
  have hd := remaining_phase_test s hs hn
  obtain ⟨δ,hδ⟩ : ∃ δ : Fin 4,phaseTest s δ := by
    rcases hd with h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  obtain ⟨p,hp⟩ := shifted_in_family s δ hδ
  have hc : complexShiftedOdd s δ=complexOdd (familyState p) := by
    rw [←complexShiftedOdd_zero]
    funext x
    exact congrArg (fun f : Signature AlgebraicComplex 4 => (f x : ℂ)) hp
  exact ⟨δ,shiftedOdd_affine s δ hδ,by rw [hc]; exact family_rank_or_dense p⟩

end Holant.Certificates.FourthRootOdd
