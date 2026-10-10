import Holant.Proofs.Hardness.ThreeModeChain
import Holant.Proofs.Hardness.ThreeModeNetworkFilter
import Holant.Proofs.Hardness.ExactTwoChainQueries

/-! Literal original-graph interpolation identity for three-mode EO chains.
Every query is the accepted serialized all-occurrence q/native-X substitution.
This file identifies the finite algebraic filter; it does not itself claim a
polynomial-time field programme or a hardness reduction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeGraphEvaluation
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace Q
export ExactTwoChainQueries (arity Input TargetInput value sourceEncoding targetEncoding)
end Q
namespace S
export ThreeModeSignatures (original spectral spectral_linear)
export ExactTwoSignatures (E B)
export SignedTwoCoefficientSignatures (Bminus)
end S
namespace RP
export Holant.LocalDrafts.BinaryInterpolation.RawPolynomial (marked marked_card replacement_same_arity)
end RP
namespace A
export ThreeModeAnnihilator (polynomial queryCount denominator denominator_ne_zero)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K : Type} [Field K] [CharZero K]
variable (a b c : K)

def targetSignatures (_i : Fin 1) : Signature K (Q.arity _i.val) := S.original a b c
def sourceSignatures (i : Fin 2) : Signature K (Q.arity i.val) :=
  if i.val=1 then S.E else S.original a b c
def sequenceSignatures (k : ℕ) (i : Fin 2) : Signature K (Q.arity i.val) :=
  if i.val=1 then S.spectral (c^(k+1)) ((a+b)^(k+1)) ((b-a)^(k+1)) else S.original a b c

def kernels (_i : Fin 1) : Kernel K := Signature.disequality

def sourceValue (r : Q.Input) : K :=
  (r.val.realize r.property (sourceSignatures a b c) kernels).denote Fin.elim0

def targetValue (r : Q.TargetInput) : K :=
  (r.val.realize r.property (targetSignatures a b c) kernels).denote Fin.elim0

def queryValue (r : Q.Input) (k : ℕ) : K := targetValue a b c (Q.value (k,r))

def eigenvalues : Fin 3 → K := ![c,a+b,b-a]
def projector : Fin 3 → Signature K 4 := ![S.E,(1/2 : K) • S.B,(-1/2 : K) • S.Bminus]

theorem projector_sum (k : ℕ) :
    (fun x=>∑i : Fin 3,eigenvalues a b c i^(k+1)*projector (K:=K) i x)=
      S.spectral (c^(k+1)) ((a+b)^(k+1)) ((b-a)^(k+1)) := by
  rw [S.spectral_linear]
  funext x
  simp [eigenvalues,projector,Fin.sum_univ_succ,add_assoc]

theorem local_identity (k : ℕ) (i : Fin 2) :
    (⟨(ExactTwoChainOccurrence.templates Q.arity 1 0 0 k i.val).boundary,
      ((ExactTwoChainOccurrence.templates Q.arity 1 0 0 k i.val).network
        (ExactTwoChainQueries.template_hypotheses k i.val i.isLt).1
        (targetSignatures a b c) (kernels (K:=K))).denote⟩ : AnySignature K)=
      ⟨Q.arity i.val,(if i.val=1 then (1 : K) else 1) • sequenceSignatures a b c k i⟩ := by
  fin_cases i
  · change (⟨4,((identityTemplate Q.arity 0).network
        (identityTemplate_wellFormed Q.arity (0 : Fin 1))
        (targetSignatures a b c) (kernels (K:=K))).denote⟩ : AnySignature K)=
      ⟨4,(1 : K) • S.original a b c⟩
    simp only [one_smul]
    apply congrArg (fun f : Signature K 4=>(⟨4,f⟩ : AnySignature K))
    exact identityTemplate_denote Q.arity (0 : Fin 1) (targetSignatures a b c) kernels
  · change (⟨4,((ExactTwoChainRecords.explicitTemplate 0 0 k).network
        (ExactTwoChainRecords.valid Q.arity (0 : Fin 1) rfl (0 : Fin 1) k)
        (targetSignatures a b c) (kernels (K:=K))).denote⟩ : AnySignature K)=
      ⟨4,(1 : K) • S.spectral (c^(k+1)) ((a+b)^(k+1)) ((b-a)^(k+1))⟩
    simp only [one_smul]
    apply congrArg (fun f : Signature K 4=>(⟨4,f⟩ : AnySignature K))
    exact ThreeModeChain.denote Q.arity (0 : Fin 1) rfl (0 : Fin 1) a b c k
      (targetSignatures a b c) kernels rfl rfl

theorem query_value (r : Q.Input) (k : ℕ) :
    queryValue a b c r k=
      (r.val.realize r.property (sequenceSignatures a b c k) kernels).denote Fin.elim0 := by
  obtain ⟨hq,he⟩ := RP.replacement_same_arity r.val r.property
    (sequenceSignatures a b c k) kernels 1
    (ExactTwoChainOccurrence.templates Q.arity 1 0 0 k)
    (fun i hi=>(ExactTwoChainQueries.template_hypotheses k i hi).1)
    (ExactTwoChainQueries.template_arity k) (targetSignatures a b c) 1 (local_identity a b c k)
  simpa only [queryValue,targetValue,Q.value,ExactTwoChainOccurrence.raw_eq_replace,
    one_pow,one_mul] using he

def originalNetwork (r : Q.Input) : Network K 0 :=
  r.val.realize r.property (sourceSignatures a b c) kernels

def modes (r : Q.Input) : Fin 3 → (v : Fin (originalNetwork a b c r).shape.vertices) →
    Signature K ((originalNetwork a b c r).shape.arity v) := fun i _v=>projector i

theorem sequence_denote (r : Q.Input) (k : ℕ) :
    (ThreeModeExpansion.sequenceNetwork (originalNetwork a b c r)
      (RP.marked r.val 1) (modes a b c r) (eigenvalues a b c) k).denote=
      (r.val.realize r.property (sequenceSignatures a b c k) kernels).denote := by
  apply Network.denote_congr (r.val.shape r.property)
  · intro v x
    change (if v∈RP.marked r.val 1 then
      ∑i : Fin 3,eigenvalues a b c i^(k+1)*projector i x else
        sourceSignatures a b c (r.val.signatureLabel r.property v) x)=
      sequenceSignatures a b c k (r.val.signatureLabel r.property v) x
    rw [congrFun (projector_sum a b c k) x]
    by_cases hv : (r.val.vertices.get v).1=1 <;>
      simp_all [RP.marked,sourceSignatures,sequenceSignatures,RawClosedNetwork.signatureLabel]
  · intros
    rfl

omit [CharZero K] in
theorem desired_denote (r : Q.Input) :
    (BinaryInterpolation.rightNetwork (originalNetwork a b c r)
      (RP.marked r.val 1) (modes a b c r 0)).denote=
      (originalNetwork a b c r).denote := by
  apply Network.denote_congr (r.val.shape r.property)
  · intro v x
    change (if v∈RP.marked r.val 1 then projector (K:=K) 0 x else
      sourceSignatures a b c (r.val.signatureLabel r.property v) x)=
      sourceSignatures a b c (r.val.signatureLabel r.property v) x
    by_cases hv : (r.val.vertices.get v).1=1 <;>
      simp_all [RP.marked,projector,sourceSignatures,RawClosedNetwork.signatureLabel]
  · intros
    rfl

/-- The full original graph identity; no interpolation success is assumed. -/
theorem numerator_identity (r : Q.Input) :
    (∑k∈Finset.range (A.queryCount (occurrences 1 r.val) c (a+b) (b-a)),
      (A.polynomial (occurrences 1 r.val) c (a+b) (b-a)).coeff k*queryValue a b c r k)=
      sourceValue a b c r*A.denominator (occurrences 1 r.val) c (a+b) (b-a) := by
  have h := ThreeModeNetworkFilter.numerator_identity (originalNetwork a b c r)
    (RP.marked r.val 1) (modes a b c r) (eigenvalues a b c) Fin.elim0
  simp_rw [sequence_denote a b c r] at h
  rw [desired_denote a b c r,RP.marked_card r.val 1] at h
  change (∑k∈Finset.range (A.queryCount (occurrences 1 r.val) c (a+b) (b-a)),
    (A.polynomial (occurrences 1 r.val) c (a+b) (b-a)).coeff k*
    (r.val.realize r.property (sequenceSignatures a b c k) kernels).denote Fin.elim0)=
    sourceValue a b c r*A.denominator (occurrences 1 r.val) c (a+b) (b-a) at h
  simpa only [query_value] using h

/-- The exact correction is division by c^m P(c^m), with no hidden scalar. -/
theorem recovery (r : Q.Input)
    (hd : A.denominator (occurrences 1 r.val) c (a+b) (b-a)≠0) :
    (∑k∈Finset.range (A.queryCount (occurrences 1 r.val) c (a+b) (b-a)),
      (A.polynomial (occurrences 1 r.val) c (a+b) (b-a)).coeff k*queryValue a b c r k)/
      A.denominator (occurrences 1 r.val) c (a+b) (b-a)=sourceValue a b c r := by
  rw [numerator_identity,mul_div_cancel_right₀ _ hd]

/-- An explicit original-coefficient dominance condition derives success.
No complex embedding, infinite-order certificate, or evaluator is supplied. -/
theorem dominant_recovery {L : Type} [NormedField L] [CharZero L]
    (a b c : L) (hplus : ‖a+b‖<‖c‖) (hminus : ‖b-a‖<‖c‖) (r : Q.Input) :
    (∑k∈Finset.range (A.queryCount (occurrences 1 r.val) c (a+b) (b-a)),
      (A.polynomial (occurrences 1 r.val) c (a+b) (b-a)).coeff k*queryValue a b c r k)/
      A.denominator (occurrences 1 r.val) c (a+b) (b-a)=sourceValue a b c r :=
  recovery a b c r (A.denominator_ne_zero hplus hminus)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeGraphEvaluation
