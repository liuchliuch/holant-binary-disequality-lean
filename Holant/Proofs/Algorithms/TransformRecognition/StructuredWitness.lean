import Holant.Proofs.Algorithms.TransformRecognition.StructuredDovetail


namespace Holant.LocalDrafts.MainChain.TransformRecognition.StructuredWitness
open Holant Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
open ComplexIsolation PowerArithmetic
variable {m k : ℕ}

structure Output (d k : ℕ) where
  root : RootCode
  relation : Vector d
  coordinates : MatrixWitness.Output d k

def emit (c : PositiveWitnessSearch.Candidate m k) : Output c.1.1 k :=
  ⟨c.2.rootCode (relationCode c.1.2.1),c.1.2.1,
    MatrixWitness.output c.1.2.1 c.1.2.2.2.2⟩

def atHeight (target : Fin m → RootCode) (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    Option (PositiveWitnessSearch.Candidate m k) :=
  (StructuredCatalogue.positive m k h).find? (PositiveWitnessSearch.check target S)

theorem atHeight_checked (target : Fin m → RootCode) (S : EncodedSystem.System m (5+k))
    (h : ℕ) (c : PositiveWitnessSearch.Candidate m k) (hc : atHeight target S h=some c) :
    PositiveWitnessSearch.check target S c=true := List.find?_some hc

def candidate (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    Option (PositiveWitnessSearch.Candidate m k) :=
  atHeight target (EncodedGuard.augment oneSlot negSlot S)
    (Nat.find (StructuredDovetail.terminates target oneSlot negSlot S hv))

def output (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    Option (Σ d, Output d k) :=
  (candidate target oneSlot negSlot S hv).map (fun c => ⟨c.1.1,emit c⟩)

theorem candidate_isSome (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    (candidate target oneSlot negSlot S hv).isSome=true ↔
      StructuredDovetail.answer target oneSlot negSlot S hv=true := by
  have hs := StructuredDovetail.answer_stage target oneSlot negSlot S hv
  let h := Nat.find (StructuredDovetail.terminates target oneSlot negSlot S hv)
  let T := EncodedGuard.augment oneSlot negSlot S
  have hp : (candidate target oneSlot negSlot S hv).isSome=true ↔
      StructuredDovetail.positive target T h=true := by
    simp only [candidate,atHeight,StructuredDovetail.positive,List.find?_isSome,List.any_eq_true,h,T]
  rw [hp]
  change StructuredDovetail.stage target T h=some (StructuredDovetail.answer target oneSlot negSlot S hv) at hs
  by_cases ha : StructuredDovetail.positive target T h=true
  · have he : StructuredDovetail.answer target oneSlot negSlot S hv=true := by
      simpa [StructuredDovetail.stage,ha] using hs.symm
    exact iff_of_true ha he
  · have he : StructuredDovetail.answer target oneSlot negSlot S hv≠true := by
      intro ht
      rw [ht] at hs
      by_cases hn : StructuredDovetail.negative target T h=true
      · have hf : (some false : Option Bool)=some true := by
          simpa only [StructuredDovetail.stage,if_neg ha,if_pos hn] using hs
        exact Bool.noConfusion (Option.some.inj hf)
      · have hn' : (none : Option Bool)=some true := by
          simpa only [StructuredDovetail.stage,if_neg ha,if_neg hn] using hs
        cases hn'
    exact iff_of_false ha he

/-- A successful certificate yields a genuinely algebraic root, the two
inverse identities and the ORIGINAL system at the encoded coordinate values.
The proof does not assume that the proposed relation defines a field. -/
theorem emit_sound (target : Fin m → RootCode) (w : Fin m → AlgebraicComplex)
    (ht : ∀ i, (target i).Represents (w i : ℂ)) (S : EncodedSystem.System m (5+k))
    (c : PositiveWitnessSearch.Candidate m k) (hc : PositiveWitnessSearch.check target S c=true) :
    ∃ θ : AlgebraicComplex, (emit c).root.Represents (θ : ℂ) ∧
      θ^(c.1.1+1)=decode θ (emit c).relation ∧
      (Kernel.mul (fun u v => decode θ ((emit c).coordinates.matrix u v))
        (fun u v => decode θ ((emit c).coordinates.inverse u v))=Signature.equality ∧
      Kernel.mul (fun u v => decode θ ((emit c).coordinates.inverse u v))
        (fun u v => decode θ ((emit c).coordinates.matrix u v))=Signature.equality) ∧
      ∀ e ∈ S, MvPolynomial.aeval (fun i => (decode θ (c.1.2.2.2.2 i) : ℂ))
        (EncodedSystem.polynomial (fun i => (w i : ℂ)) e)=0 := by
  simp only [PositiveWitnessSearch.check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨hbox,hroot,hpre⟩ := hc
  obtain ⟨z,hz⟩ := Certificate.check_sound hroot
  let θ : AlgebraicComplex := ⟨z,mem_algebraicClosure_iff.mpr (RootCode.represents_isAlgebraic hz)⟩
  have hrC : z^(c.1.1+1)=decode z c.1.2.1 := by
    apply relation_of_root
    simpa only [RootCode.polynomial,Certificate.rootCode,relationCode_polynomial] using hz.2.2.1
  have hr : θ^(c.1.1+1)=decode θ c.1.2.1 := by
    apply Subtype.val_injective
    change z^(c.1.1+1)=(decode θ c.1.2.1 : ℂ)
    rw [MatrixWitness.decode_coe]
    exact hrC
  have hsource : c.1.2.2.1.Contains (θ : ℂ) := by
    rw [hbox]
    exact RationalBox.contains_ofRectangle hz.2.1
  have hs := MatrixWitness.checkCandidate_sound c.1.2.1 c.1.2.2.1 c.1.2.2.2.1
    target S c.1.2.2.2.2 θ w hr hsource ht hpre
  exact ⟨θ,hz,hr,hs.1,hs.2⟩

theorem candidate_sound (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot)
    (c : PositiveWitnessSearch.Candidate m k) (hc : candidate target oneSlot negSlot S hv=some c) :
    PositiveWitnessSearch.check target (EncodedGuard.augment oneSlot negSlot S) c=true :=
  atHeight_checked target _ _ c hc

end Holant.LocalDrafts.MainChain.TransformRecognition.StructuredWitness
