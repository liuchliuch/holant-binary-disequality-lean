import Holant.OpenNetworkComposition.FactorFreeNormalization.Reduction
import Holant.Complexity.UniversalPairReduction.OrderedGadget
import Mathlib.Tactic.FinCases

/-! The asymmetric branch may start from an arbitrary actual open realization.
Asymmetry excludes its only possible isolated free/free wire factor, so ordinary
normalization needs no supplied identity signature. -/
noncomputable section
namespace Holant.Complexity.UniversalPairReduction
open OpenNetworkComposition.FactorFreeNormalization FixedGadgetSubstitution
variable {K : Type*} [CommSemiring K]

/-- At binary arity, an isolated native-X factor has equal off-diagonal entries,
including arbitrary zero or nonzero scalar values of all other components. -/
theorem symmetric_of_hasXFactor (f : Signature K 2) (h : HasXFactor f) :
    f ![false,true] = f ![true,false] := by
  obtain ⟨i,j,hij,g,hg⟩ := h
  have other_empty : IsEmpty (OtherPorts i j) := by
    refine ⟨fun k => ?_⟩
    rcases k with ⟨k,hki,hkj⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  letI := other_empty
  have hx : (fun k : OtherPorts i j => (![false,true] : Fin 2 → Bool) k.val) =
      (fun k : OtherPorts i j => (![true,false] : Fin 2 → Bool) k.val) :=
    Subsingleton.elim _ _
  rw [hg,hg,hx]
  fin_cases i <;> fin_cases j <;> simp_all [Signature.disequality]

theorem asymmetric_noXFactor (f : Signature K 2)
    (h : f ![false,true] ≠ f ![true,false]) : NoXFactor f :=
  fun hx => h (symmetric_of_hasXFactor f hx)

/-- Actual finite-network provenance produces an ordinary native-X witness;
there is no equality-resource, nonzero-scalar, or already-normalized premise. -/
theorem asymmetric_ordinary_witness (family : SignatureFamily K) (f : Signature K 2)
    (hf : Gadget.Realizes family .disequality f)
    (ha : f ![false,true] ≠ f ![true,false]) :
    ∃N : Network K 2,
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote=f :=
  realizes_exists_ordinary hf (asymmetric_noXFactor f ha)

/-- This is the exact exhaustive split used by the source proof; its witness
is a physical ordinary network over the original family. -/
theorem actual_binary_dichotomy (family : SignatureFamily K) :
    (∀f : Signature K 2, Gadget.Realizes family .disequality f →
      f ![false,true]=f ![true,false]) ∨
    ∃N : Network K 2,
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
      (∀e,N.edge e=Signature.disequality) ∧
      N.denote ![false,true]≠N.denote ![true,false] := by
  classical
  by_cases h : ∀f : Signature K 2, Gadget.Realizes family .disequality f →
      f ![false,true]=f ![true,false]
  · exact Or.inl h
  · push_neg at h
    obtain ⟨f,hf,ha⟩ := h
    obtain ⟨N,hv,he,hN⟩ := asymmetric_ordinary_witness family f hf ha
    exact Or.inr ⟨N,hv,he,by simpa [hN] using ha⟩

end Holant.Complexity.UniversalPairReduction
