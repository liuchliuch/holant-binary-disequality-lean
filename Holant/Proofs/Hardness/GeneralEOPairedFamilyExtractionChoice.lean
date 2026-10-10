import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionTensor
import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyFieldClosed

/-! For every incompatible finite nonzero closed-support family, choose two
actual original labels internally and form one nonzero compressed tensor
outside both classes. No hard row, pin, triangle, or minor is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionChoice
open Holant Holant.Tractable
namespace T
export GeneralEOPairedFamilyExtractionTensor (tensor tensor_nonzero tensor_failures)
end T
namespace C
export GeneralEOPairedCSPFamilyFieldClosed (pairing covers)
end C
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem restrict_nonzero (p : OrientedPerfectPairing n) (g : Signature AlgebraicComplex n)
    (hg : g≠0) (hp : GeneralEOPairedCSPCycles.Covers p g) : p.restrict g≠0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hg
  intro hz
  have hh := congrFun hz (Holant.LocalDrafts.Tractability.EOEvaluation.PairLift.compress p x)
  simp only [OrientedPerfectPairing.restrict,
    Holant.LocalDrafts.Tractability.EOEvaluation.PairLift.word_compress p x (hp x hx),
    Pi.zero_apply] at hh
  exact hx hh

theorem word_tripleXor (p : OrientedPerfectPairing n)
    (x y z : Fin p.count → Bool) :
    p.word (tripleXor x y z) = tripleXor (p.word x) (p.word y) (p.word z) := by
  funext i
  obtain ⟨⟨j,b⟩,rfl⟩ := p.ports.surjective i
  cases b <;> cases hx : x j <;> cases hy : y j <;> cases hz : z j <;>
    simp [OrientedPerfectPairing.word, tripleXor, hx, hy, hz]

theorem restrict_closed (p : OrientedPerfectPairing n) (g : Signature AlgebraicComplex n)
    (hg : GeneralEONegativeClosedSupport.Closed g) :
    GeneralEONegativeClosedSupport.Closed (p.restrict g) := by
  intro x y z hx hy hz
  change g (p.word (tripleXor x y z))≠0
  rw [word_tripleXor]
  exact hg _ _ _ hx hy hz

theorem tensor_closed {m : ℕ} (f : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n)
    (hf : GeneralEONegativeClosedSupport.Closed f)
    (hg : GeneralEONegativeClosedSupport.Closed g) :
    GeneralEONegativeClosedSupport.Closed (T.tensor f g) := by
  intro x y z hx hy hz
  exact mul_ne_zero
    (hf _ _ _ (mul_ne_zero_iff.mp hx).1 (mul_ne_zero_iff.mp hy).1 (mul_ne_zero_iff.mp hz).1)
    (hg _ _ _ (mul_ne_zero_iff.mp hx).2 (mul_ne_zero_iff.mp hy).2 (mul_ne_zero_iff.mp hz).2)

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))

abbrev compressed (i : Fin s) := (C.pairing G he hn hc i).restrict (G i)

variable (ha : ¬∀i,Affine (compressed G he hn hc i))
variable (hp : ¬∀i,Product (compressed G he hn hc i))

def leftLabel : Fin s := Classical.choose (not_forall.mp ha)
def rightLabel : Fin s := Classical.choose (not_forall.mp hp)

theorem left_failure : ¬Affine (compressed G he hn hc (leftLabel G he hn hc ha)) :=
  Classical.choose_spec (not_forall.mp ha)
theorem right_failure : ¬Product (compressed G he hn hc (rightLabel G he hn hc hp)) :=
  Classical.choose_spec (not_forall.mp hp)

def extracted := T.tensor
  (compressed G he hn hc (leftLabel G he hn hc ha))
  (compressed G he hn hc (rightLabel G he hn hc hp))

theorem compressed_nonzero (i : Fin s) : compressed G he hn hc i≠0 :=
  restrict_nonzero _ _ (hn i) (C.covers G he hn hc i)

theorem extracted_nonzero : extracted G he hn hc ha hp≠0 :=
  T.tensor_nonzero (compressed_nonzero G he hn hc _) (compressed_nonzero G he hn hc _)

theorem extracted_closed : GeneralEONegativeClosedSupport.Closed (extracted G he hn hc ha hp) :=
  tensor_closed _ _ (restrict_closed _ _ (hc _)) (restrict_closed _ _ (hc _))

/-- Generic mixed-family extraction. It does not assert that an original
single row or one-row cap already fails both classes. -/
theorem extracted_failures :
    ¬Affine (extracted G he hn hc ha hp) ∧ ¬Product (extracted G he hn hc ha hp) :=
  T.tensor_failures (compressed_nonzero G he hn hc _) (compressed_nonzero G he hn hc _)
    (left_failure G he hn hc ha) (right_failure G he hn hc hp)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionChoice
