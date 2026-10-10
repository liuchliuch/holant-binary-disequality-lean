import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseChoice

/-! Internally constructed literal recipes for hard binary CSP signatures.
The syntax retains every original-coordinate minor and whether one private
Boolean variable is summed. It is not an assumed oracle or hardness witness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionRecipe
open Holant Holant.Tractable
open scoped BigOperators
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose substitute_compose hardPorts hard_spec)
end I
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
namespace C
export GeneralEOPairedFamilyExtractionComponentsFull (reduced substitution expand_substitute reduced_full reduced_failures)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

inductive Recipe (n : ℕ) where
  | direct : List (Fin n → Bool ⊕ Fin 2) → Recipe n
  | marginal : List (Fin n → Bool ⊕ Fin 3) → Recipe n

variable {n k : ℕ}

def denote {K : Type*} [CommSemiring K] (f : Signature K n) : Recipe n → Signature K 2
  | .direct ps => B.evaluate f ps
  | .marginal ps => fun z => ∑b : Bool,B.evaluate f ps (Fin.snoc z b)

def lift (p : Fin n → Bool ⊕ Fin k) : Recipe k → Recipe n
  | .direct ps => .direct (ps.map (fun q => I.compose p q))
  | .marginal ps => .marginal (ps.map (fun q => I.compose p q))

theorem lift_value {K : Type*} [CommSemiring K] (f : Signature K n)
    (p : Fin n → Bool ⊕ Fin k) (r : Recipe k) :
    denote f (lift p r)=denote (fun x=>f (T.substitute p x)) r := by
  cases r <;> funext z <;> simp only [denote,lift,B.evaluate,List.map_map,Function.comp_def,I.substitute_compose]

def Bad (f : Signature AlgebraicComplex n) (r : Recipe n) : Prop :=
  ¬Affine (denote f r) ∧ ¬Product (denote f r)

theorem nonaffine_scale (f : Signature AlgebraicComplex 2) (hf : ¬Affine f)
    (c : AlgebraicComplex) (hc : c≠0) : ¬Affine (fun z=>c*f z) := by
  intro h
  apply hf
  convert h.scale c⁻¹ using 1
  funext z
  simp only [←mul_assoc,inv_mul_cancel₀ hc,one_mul]

theorem nonproduct_scale (f : Signature AlgebraicComplex 2) (hf : ¬Product f)
    (c : AlgebraicComplex) (hc : c≠0) : ¬Product (fun z=>c*f z) := by
  intro h
  apply hf
  convert h.scale c⁻¹ using 1
  funext z
  simp only [←mul_assoc,inv_mul_cancel₀ hc,one_mul]

variable (f : Signature AlgebraicComplex n)

theorem exists_full_phase (hf : ∀x,f x≠0) (ha : ¬Affine f)
    (hp : ∀x,f x^4=f (AffinePhase.origin n)^4) : ∃r : Recipe n,Bad f r := by
  rcases GeneralEOPairedFamilyExtractionPhaseChoice.alternatives f hf ha hp with hb|ht
  · obtain ⟨p,_,ha,hp⟩ := hb
    have he : denote f (.direct [p])=(fun z => f (T.substitute p z)) := by
      funext z
      simp only [denote,B.evaluate,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    refine ⟨.direct [p],?_⟩
    unfold Bad
    rw [he]
    exact ⟨ha,hp⟩
  · obtain ⟨ps,c,δ,hc,hfour,hn,he⟩ := ht
    refine ⟨.marginal ps,?_⟩
    have hv : denote f (.marginal ps)=fun z=>c*GeneralEOPairedFamilyExtractionPhaseTrace.binary δ z := by
      funext z
      change (∑b : Bool,B.evaluate f ps (Fin.snoc z b))=_
      simp_rw [he]
      rw [Fintype.sum_bool]
      have hh (b : Bool) : Fin.snoc z b=![z 0,z 1,b] := by funext i; fin_cases i <;> rfl
      simp only [hh]
      calc
        _=c*(GeneralEOPairedFamilyExtractionPhaseTrace.monomial δ ![z 0,z 1,false]+
            GeneralEOPairedFamilyExtractionPhaseTrace.monomial δ ![z 0,z 1,true]) := by
          simp only [GeneralEOPairedFamilyExtractionPhaseTrace.monomial]; ring
        _=_ := congrArg (c*·) (GeneralEOPairedFamilyExtractionPhaseTrace.trace δ z)
    unfold Bad
    rw [hv]
    exact ⟨nonaffine_scale _ (GeneralEOPairedFamilyExtractionPhaseTrace.not_affine δ hfour hn) c hc,
      nonproduct_scale _ (GeneralEOPairedFamilyExtractionPhaseTrace.not_product δ hn) c hc⟩

/-- Both arbitrary full-support branches are now literal recipes: direct
weighted interaction or an internally isolated higher phase and one trace. -/
theorem exists_full (hf : ∀x,f x≠0) (ha : ¬Affine f) (hp : ¬Product f) : ∃r : Recipe n,Bad f r := by
  by_cases hpow : ∀x,f x^4=f (AffinePhase.origin n)^4
  · exact exists_full_phase f hf ha hpow
  · have hw : ¬GeneralEOPairedFamilyExtractionWeight.CommonFourthSupport f := by
      intro h
      exact hpow (fun x=>h x (hf x))
    have hx : GeneralEOPairedFamilyExtractionSupport.XorClosed f := fun _ _ _ _=>hf _
    have hm : GeneralEOPairedFamilyExtractionSupport.MeetClosed f := fun _ _ _ _=>hf _
    refine ⟨.direct (I.hardPorts f (hf _) hx hm hp hw),?_⟩
    exact (I.hard_spec f (hf _) hx hm hp hw).2

theorem exists_meet_closed (h0 : f GeneralEOPairedFamilyExtractionSupport.origin≠0)
    (hx : GeneralEOPairedFamilyExtractionSupport.XorClosed f)
    (hm : GeneralEOPairedFamilyExtractionSupport.MeetClosed f) (ha : ¬Affine f) (hp : ¬Product f) :
    ∃r : Recipe n,Bad f r := by
  obtain ⟨r,hr⟩ := exists_full (C.reduced f) (C.reduced_full f h0 hx hm)
    (C.reduced_failures f ha hp).1 (C.reduced_failures f ha hp).2
  refine ⟨lift (C.substitution f) r,?_⟩
  unfold Bad
  rw [lift_value]
  have he : (fun x => f (T.substitute (C.substitution f) x))=C.reduced f := by
    funext x
    rw [←C.expand_substitute]
    rfl
  rw [he]
  exact hr

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionRecipe
