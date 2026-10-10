import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseChoice
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicCore

/-! Literal phase extraction for arbitrary full-support nonaffine signatures
with constant nonzero square. The phase bundle is retained exactly, including
its positive multiplicities and its power of the original coefficient. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeCubicExtraction
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace C
export GeneralEOPairedFamilyExtractionPhaseChoice
  (normalized normalized_origin normalized_four normalized_not_affine denormalize)
end C
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle
  (evaluate evaluate_scale evaluate_compose ports ports_value)
end B
namespace N
export GeneralEOPairedFamilyExtractionPhaseNormalization
  (Edge pairTable residual unary unary_affine affine_prod)
end N
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose)
end I
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace A
export AffinePhase (origin word basis)
end A
namespace P
export EOBinaryPlaneClassification (Full SignedCross Cross full_affine_iff)
end P
open OrdinaryNegativeCubicCore
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

variable {n : ℕ}

theorem fourth_of_square (f : Signature AlgebraicComplex n)
    (hsq : ∀x,f x^2=f (A.origin n)^2) (x : Fin n → Bool) :
    f x^4=f (A.origin n)^4 := by
  calc
    f x^4=(f x^2)^2 := by ring
    _=(f (A.origin n)^2)^2 := congrArg (fun z : AlgebraicComplex => z^2) (hsq x)
    _=f (A.origin n)^4 := by ring

theorem normalized_square (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0)
    (hsq : ∀x,f x^2=f (A.origin n)^2) (x : Fin n → Bool) : C.normalized f x^2=1 := by
  rw [C.normalized,mul_pow,inv_pow,hsq x,inv_mul_cancel₀ (pow_ne_zero 2 (hf _))]

/-- Every full-support binary sign table is an actual affine quadratic. -/
theorem binary_square_affine (g : Signature AlgebraicComplex 2)
    (hsq : ∀x,g x^2=1) : Affine g := by
  have hf : P.Full g := by
    intro x hz
    have h := hsq x
    norm_num [hz] at h
  apply (P.full_affine_iff g hf).mpr
  constructor
  · intro x
    have hh (z : Fin 2 → Bool) : g z^4=1 := by
      calc
        g z^4=(g z^2)^2 := by ring
        _=1 := by rw [hsq]; norm_num
    rw [hh,hh]
  · apply sq_eq_sq_iff_eq_or_eq_neg.mp
    simp only [mul_pow,hsq,one_mul]

theorem normalized_pair_affine (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0)
    (hsq : ∀x,f x^2=f (A.origin n)^2) (e : N.Edge n) :
    Affine (N.pairTable (C.normalized f) e) := by
  apply binary_square_affine
  intro z
  rw [←GeneralEOPairedFamilyExtractionPhaseChoice.pair_value _ (C.normalized_origin f hf) e z]
  exact normalized_square f hf hsq _

/-- Positive products retain the constant-square invariant, regardless of
which coordinates are pinned or identified in their literal substitutions. -/
theorem evaluate_square {m : ℕ} (g : Signature AlgebraicComplex n)
    (hsq : ∀x,g x^2=1) (ps : List (Fin n → Bool ⊕ Fin m)) (z : Fin m → Bool) :
    B.evaluate g ps z^2=1 := by
  induction ps with
  | nil => simp [B.evaluate]
  | cons p ps ih =>
      change (g (T.substitute p z)*B.evaluate g ps z)^2=1
      rw [mul_pow,hsq,ih,one_mul]

def extractionPorts (p : Fin n → Bool ⊕ Fin 3) : List (Fin n → Bool ⊕ Fin 3) :=
  B.ports.map (fun q => I.compose q p)

def extractionScale (f : Signature AlgebraicComplex n) (p : Fin n → Bool ⊕ Fin 3) :
    AlgebraicComplex := f (A.origin n)^(extractionPorts p).length

/-- The internal ternary phase choice has negative sign, and the exact fixed
positive list realizes a nonzero scalar times the cubic sign. -/
theorem exists_cubic_bundle (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0)
    (hsq : ∀x,f x^2=f (A.origin n)^2) (ha : ¬Affine f) :
    ∃p : Fin n → Bool ⊕ Fin 3,
      extractionScale f p≠0 ∧ ∀z : Fin 3 → Bool,
        B.evaluate f (extractionPorts p) z=extractionScale f p*cubic z := by
  have hfour := C.normalized_four f hf (fourth_of_square f hsq)
  obtain ⟨p,δ,hδ,hn,he⟩ := GeneralEOPairedFamilyExtractionPhaseSmall.exists_ternary
    (C.normalized f) (C.normalized_origin f hf) hfour
    (C.normalized_not_affine f hf ha) (normalized_pair_affine f hf hsq)
  have hv (z : Fin 3 → Bool) : B.evaluate (C.normalized f) (extractionPorts p) z=
      if z=![true,true,true] then δ else 1 := by
    rw [extractionPorts,B.evaluate_compose,B.ports_value _ (C.normalized_origin f hf) hfour,he]
  have hd : δ^2=1 := by
    have hh := evaluate_square (C.normalized f) (normalized_square f hf hsq)
      (extractionPorts p) ![true,true,true]
    simpa only [hv,ite_true] using hh
  have hdneg : δ = -1 := (sq_eq_one_iff.mp hd).resolve_left hn
  refine ⟨p,pow_ne_zero _ (hf _),?_⟩
  intro z
  have hs := B.evaluate_scale (C.normalized f) (f (A.origin n)) (extractionPorts p) z
  rw [←C.denormalize f hf,hv,hdneg] at hs
  rw [hs]
  congr 1
  have hz : z=![true,true,true] ↔ (z 0 && z 1 && z 2)=true := by
    constructor
    · intro h
      simp [h]
    · intro h
      simp only [Bool.and_eq_true] at h
      funext i
      fin_cases i <;> simp [h.1.1,h.1.2,h.2]
  simp only [cubic,hz]

/-- Every binary literal minor of a constant-square signature is affine. -/
theorem binary_minor_affine (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0)
    (hsq : ∀x,f x^2=f (A.origin n)^2) (p : Fin n → Bool ⊕ Fin 2) :
    Affine (fun z => f (T.substitute p z)) := by
  have h := binary_square_affine (fun z => C.normalized f (T.substitute p z))
    (fun z => normalized_square f hf hsq _)
  convert h.scale (f (A.origin n)) using 1
  funext z
  simp only [C.normalized,←mul_assoc,mul_inv_cancel₀ (hf _),one_mul]

/-- The parity sign is affine in every arity, including zero. -/
def paritySign (n : ℕ) : Signature AlgebraicComplex n :=
  fun x => ∏i,if x i then (-1 : AlgebraicComplex) else 1

theorem paritySign_affine (n : ℕ) : Affine (paritySign n) := by
  apply N.affine_prod (fun i => N.unary (fun _ : Fin n → Bool => (-1 : AlgebraicComplex)) i)
  intro i
  apply N.unary_affine
  intro x
  norm_num

theorem paritySign_word (s : Finset (Fin n)) :
    paritySign n (A.word s)=(-1 : AlgebraicComplex)^s.card := by
  simp [paritySign,A.word]

theorem word_update_false (s : Finset (Fin n)) (j : Fin n) (hj : j∉s) :
    Function.update (A.word s) j false=A.word s := by
  convert Function.update_eq_self j (A.word s) using 1
  simp [A.word,hj]

theorem word_update_true (s : Finset (Fin n)) (j : Fin n) :
    Function.update (A.word s) j true=A.word (insert j s) := by
  funext k
  by_cases hk : k=j
  · subst k
    simp [A.word]
  · simp [A.word,hk]

/-- If every edge of the Boolean cube negates a coefficient, the function
is exactly a scalar times parity and is therefore affine. -/
theorem affine_of_adjacent_neg (f : Signature AlgebraicComplex n)
    (hneg : ∀x : Fin n → Bool,∀j : Fin n,
      f (Function.update x j true) = -f (Function.update x j false)) : Affine f := by
  have hv (s : Finset (Fin n)) : f (A.word s)=f (A.origin n)*(-1 : AlgebraicComplex)^s.card := by
    induction s using Finset.induction_on with
    | empty => simp only [AffinePhase.word_empty,Finset.card_empty,pow_zero,mul_one]
    | @insert j s hj ih =>
        rw [←word_update_true,hneg,word_update_false s j hj,ih,
          Finset.card_insert_of_notMem hj,pow_succ]
        ring
  have he : f=(fun x => f (A.origin n)*paritySign n x) := by
    funext x
    rw [←GeneralEOPairedFamilyExtractionPhaseMinor.word_support x,hv,paritySign_word]
  rw [he]
  exact (paritySign_affine n).scale _

/-- A nonaffine constant-square signature has an actual one-coordinate
pinning face with two equal nonzero values. -/
theorem exists_positive_face (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0)
    (hsq : ∀x,f x^2=f (A.origin n)^2) (ha : ¬Affine f) :
    ∃j : Fin n,∃x : Fin n → Bool,
      f (Function.update x j false)≠0 ∧
        f (Function.update x j true)=f (Function.update x j false) := by
  by_contra hn
  apply ha
  apply affine_of_adjacent_neg
  intro x j
  have hp : f (Function.update x j true)^2=f (Function.update x j false)^2 :=
    (hsq _).trans (hsq _).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hp with h|h
  · exact False.elim (hn ⟨j,x,hf _,h⟩)
  · exact h

/-- A genuine pinning face has precisely one exposed port. -/
def unaryPorts (j : Fin n) (x : Fin n → Bool) : Fin n → Bool ⊕ Fin 1 :=
  fun i => if i=j then Sum.inr 0 else Sum.inl (x i)

theorem unaryPorts_substitute (j : Fin n) (x : Fin n → Bool) (z : Fin 1 → Bool) :
    T.substitute (unaryPorts j x) z=Function.update x j (z 0) := by
  funext i
  by_cases hi : i=j
  · subst i
    simp [unaryPorts,T.substitute]
  · simp [unaryPorts,T.substitute,hi]

@[simp] theorem unaryPorts_live_iff (j i : Fin n) (x : Fin n → Bool) :
    unaryPorts j x i=Sum.inr 0 ↔ i=j := by
  by_cases hi : i=j <;> simp [unaryPorts,hi]

theorem unaryPorts_live_count (j : Fin n) (x : Fin n → Bool) :
    (∑i : Fin n,if unaryPorts j x i=Sum.inr 0 then 1 else 0 : ℕ)=1 := by
  simp

/-- The positive unary is supplied by one original signature with every
other port pinned, with its exact original nonzero coefficient retained. -/
theorem exists_positive_unary (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0)
    (hsq : ∀x,f x^2=f (A.origin n)^2) (ha : ¬Affine f) :
    ∃j : Fin n,∃x : Fin n → Bool,∃c : AlgebraicComplex,
      c≠0 ∧ ∀z : Fin 1 → Bool,f (T.substitute (unaryPorts j x) z)=c := by
  obtain ⟨j,x,hc,he⟩ := exists_positive_face f hf hsq ha
  refine ⟨j,x,f (Function.update x j false),hc,?_⟩
  intro z
  rw [unaryPorts_substitute]
  cases z 0
  · rfl
  · exact he

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeCubicExtraction
end
