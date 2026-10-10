import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicExtraction
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseOccurrences

/-! Internal choice of the literal cubic phase bundle in the original
intermediate field. Only the verified embedding into AlgebraicComplex is
used; the emitted rows, scalar, and even incidence remain over that field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativePhaseBundleChoice
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace E
export OrdinaryNegativeCubicExtraction (extractionPorts extractionScale exists_cubic_bundle)
end E
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
namespace O
export GeneralEOPairedFamilyExtractionPhaseOccurrences
  (occurrences even_occurrences_ports_compose four_dvd_occurrences_ports_compose)
end O
open OrdinaryNegativeCubicCore (cubic)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {n : ℕ} (K : IntermediateField ℚ AlgebraicComplex) (f : Signature K n)

abbrev origin : Fin n → Bool := AffinePhase.origin n

def ps (p : Fin n → Bool ⊕ Fin 3) : List (Fin n → Bool ⊕ Fin 3) := E.extractionPorts p

def c (p : Fin n → Bool ⊕ Fin 3) : K := f origin^(ps p).length

/-- Subtype coercion commutes with the literal positive product of minors. -/
theorem coe_evaluate {m : ℕ} (qs : List (Fin n → Bool ⊕ Fin m)) (z : Fin m → Bool) :
    ((B.evaluate f qs z : K) : AlgebraicComplex)=B.evaluate (fun x => (f x : AlgebraicComplex)) qs z := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      change ((f _*B.evaluate f qs z : K) : AlgebraicComplex)=_
      rw [IntermediateField.coe_mul,ih]
      rfl

@[simp] theorem coe_cubic (z : Fin 3 → Bool) :
    (cubic (K := K) z : AlgebraicComplex)=cubic (K := AlgebraicComplex) z := by
  unfold cubic
  split <;> simp

/-- All coefficients, including the exact extraction power, stay in K. -/
theorem exists_choice (full : ∀x,f x≠0) (square : ∀x,f x^2=f origin^2)
    (nonAffine : ¬Affine (fun x => (f x : AlgebraicComplex))) :
    ∃p : Fin n → Bool ⊕ Fin 3,
      c K f p≠0 ∧
      (∀z : Fin 3 → Bool,B.evaluate f (ps p) z=c K f p*cubic z) ∧
      (∀k : Fin 3,Even (O.occurrences (ps p) k)) := by
  have full' (x : Fin n → Bool) : (f x : AlgebraicComplex)≠0 := by
    intro h
    exact full x (Subtype.ext h)
  have square' (x : Fin n → Bool) : (f x : AlgebraicComplex)^2=
      (f origin : AlgebraicComplex)^2 := by
    simpa only [IntermediateField.coe_pow] using
      congrArg (fun y : K => (y : AlgebraicComplex)) (square x)
  obtain ⟨p,_,hp⟩ := E.exists_cubic_bundle (fun x => (f x : AlgebraicComplex))
    full' square' nonAffine
  refine ⟨p,pow_ne_zero _ (full _),?_,?_⟩
  · intro z
    apply Subtype.ext
    rw [coe_evaluate,IntermediateField.coe_mul,coe_cubic]
    simpa only [c,ps,E.extractionScale,IntermediateField.coe_pow] using hp z
  · intro k
    exact O.even_occurrences_ports_compose p k

/-- The chosen substitution carries the exact K-valued semantic equations
and actual incidence facts, with no externally supplied successful witness. -/
structure Choice where
  p : Fin n → Bool ⊕ Fin 3
  nonzero : c K f p≠0
  exact : ∀z : Fin 3 → Bool,B.evaluate f (ps p) z=c K f p*cubic z
  even : ∀k : Fin 3,Even (O.occurrences (ps p) k)

namespace Choice
variable {K f}

abbrev rows (D : Choice K f) : List (Fin n → Bool ⊕ Fin 3) := ps D.p
abbrev coefficient (D : Choice K f) : K := c K f D.p

theorem four_dvd (D : Choice K f) (k : Fin 3) : 4 ∣ O.occurrences D.rows k :=
  O.four_dvd_occurrences_ports_compose D.p k

end Choice

/-- Internal choice from the original row's stated negative-slice hypotheses. -/
def choose (full : ∀x,f x≠0) (square : ∀x,f x^2=f origin^2)
    (nonAffine : ¬Affine (fun x => (f x : AlgebraicComplex))) : Choice K f := by
  let h := exists_choice K f full square nonAffine
  exact ⟨Classical.choose h,(Classical.choose_spec h).1,
    (Classical.choose_spec h).2.1,(Classical.choose_spec h).2.2⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativePhaseBundleChoice
end
