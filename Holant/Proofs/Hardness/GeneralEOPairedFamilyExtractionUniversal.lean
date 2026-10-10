import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionGadget

/-! Every origin-supported XOR-closed row outside Affine and Product internally
constructs a finite hard binary gadget. The sparse equal-fourth case uses an
actual affine retraction and literal fourth-power parity circuits. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionUniversal
open Holant Holant.Tractable AffinePhase TwoTranslate
open scoped BigOperators
namespace S
export GeneralEOPairedFamilyExtractionSupport (origin XorClosed MeetClosed exists_parity parityRow)
end S
namespace O
export GeneralEOPairedFamilyExtractionOrigin (paritySubstitution parityWord_substitute)
end O
namespace W
export GeneralEOPairedFamilyExtractionWeight (CommonFourthSupport)
end W
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
namespace R
export GeneralEOPairedFamilyExtractionRecipe
  (Recipe Bad denote exists_full_phase exists_meet_closed nonaffine_scale nonproduct_scale)
end R
namespace G
export GeneralEOPairedFamilyExtractionGadget
  (Gadget denote Bad direct trace trace_value ofRecipe ofRecipe_bad substitute_affine affine_comp)
end G
namespace F
export GeneralEOPairedFamilyExtractionRetraction (full retraction spec full_nonzero full_not_affine full_fourth)
end F
namespace C
export GeneralEOPairedFamilyExtractionCircuit (privateCount ports value)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {n m : ℕ}

theorem exists_parity_gate (f : Signature AlgebraicComplex n) (h0 : f S.origin≠0)
    (hx : S.XorClosed f) (hm : ¬S.MeetClosed f) (hp : W.CommonFourthSupport f) :
    ∃q : Fin n → Bool ⊕ Fin 3,∀z : Word 3,
      f (T.substitute q z)^4=
        if Bool.xor (Bool.xor (z 0) (z 1)) (z 2)=false then f S.origin^4 else 0 := by
  obtain ⟨u,v,_,_,hs,_⟩ := S.exists_parity f h0 hx hm
  refine ⟨O.paritySubstitution u v,?_⟩
  intro z
  have he : f (T.substitute (O.paritySubstitution u v) z)=S.parityRow f u v z := by
    rw [←O.parityWord_substitute]
    rfl
  by_cases hz : Bool.xor (Bool.xor (z 0) (z 1)) (z 2)=false
  · have hn : f (T.substitute (O.paritySubstitution u v) z)≠0 := he ▸ (hs z).mpr hz
    simp only [hz,ite_true]
    exact hp _ hn
  · have hn : f (T.substitute (O.paritySubstitution u v) z)=0 := by
      by_contra hh
      exact hz ((hs z).mp (he ▸ hh))
    simp [hz,hn]

def circuit (ρ : Word n → Word n) (ps : List (Fin n → Bool ⊕ Fin m))
    (q : Fin n → Bool ⊕ Fin 3) : G.Gadget n m :=
  ⟨C.privateCount m n ps.length,C.ports (fun v z=>ρ (T.substitute (ps.get v) z)) q⟩

theorem circuit_value (f : Signature AlgebraicComplex n) (ρ : Word n → Word n)
    (hρ : IsAffineMap ρ) (ps : List (Fin n → Bool ⊕ Fin m)) (q : Fin n → Bool ⊕ Fin 3)
    (c : AlgebraicComplex) (hq : ∀w : Word 3,f (T.substitute q w)^4=
      if Bool.xor (Bool.xor (w 0) (w 1)) (w 2)=false then c else 0) (z : Word m) :
    G.denote f (circuit ρ ps q) z=c^(C.privateCount m n ps.length)*B.evaluate (fun x=>f (ρ x)) ps z := by
  change (∑y : Word (C.privateCount m n ps.length),B.evaluate f
    (C.ports (fun v z=>ρ (T.substitute (ps.get v) z)) q) (Fin.addCases z y))=_
  rw [C.value f q c hq _ (fun v=>G.affine_comp ρ _ hρ (G.substitute_affine (ps.get v)))]
  congr 1
  rw [←List.prod_ofFn]
  unfold B.evaluate
  apply congrArg List.prod
  exact List.ofFn_getElem_eq_map ps (fun p=>f (ρ (T.substitute p z)))

theorem exists_sparse_phase (f : Signature AlgebraicComplex n) (h0 : f S.origin≠0)
    (hx : S.XorClosed f) (hm : ¬S.MeetClosed f) (ha : ¬Affine f)
    (hp : W.CommonFourthSupport f) : ∃g : G.Gadget n 2,G.Bad f g := by
  obtain ⟨q,hq⟩ := exists_parity_gate f h0 hx hm hp
  obtain ⟨r,hr⟩ := R.exists_full_phase (F.full f h0 hx) (F.full_nonzero f h0 hx)
    (F.full_not_affine f h0 hx ha) (F.full_fourth f h0 hx hp)
  cases r with
  | direct ps =>
    let g := circuit (F.retraction f h0 hx) ps q
    have hv : G.denote f g=fun z=>(f S.origin^4)^(C.privateCount 2 n ps.length)*R.denote (F.full f h0 hx) (.direct ps) z := by
      funext z
      exact circuit_value f _ (F.spec f h0 hx).1 ps q (f S.origin^4) hq z
    refine ⟨g,?_⟩
    unfold G.Bad
    rw [hv]
    exact ⟨R.nonaffine_scale _ hr.1 _ (pow_ne_zero _ (pow_ne_zero _ h0)),
      R.nonproduct_scale _ hr.2 _ (pow_ne_zero _ (pow_ne_zero _ h0))⟩
  | marginal ps =>
    let g := G.trace (circuit (F.retraction f h0 hx) ps q)
    have hv : G.denote f g=fun z=>(f S.origin^4)^(C.privateCount 3 n ps.length)*R.denote (F.full f h0 hx) (.marginal ps) z := by
      funext z
      rw [show g=G.trace (circuit (F.retraction f h0 hx) ps q) from rfl,G.trace_value]
      simp_rw [circuit_value f _ (F.spec f h0 hx).1 ps q (f S.origin^4) hq]
      rw [←Finset.mul_sum]
      rfl
    refine ⟨g,?_⟩
    unfold G.Bad
    rw [hv]
    exact ⟨R.nonaffine_scale _ hr.1 _ (pow_ne_zero _ (pow_ne_zero _ h0)),
      R.nonproduct_scale _ hr.2 _ (pow_ne_zero _ (pow_ne_zero _ h0))⟩

/-- Universal internally constructed structural exit. There is no input gadget,
class certificate, inverse signature, or supplied hardness reduction. -/
theorem exists_gadget (f : Signature AlgebraicComplex n) (h0 : f S.origin≠0)
    (hx : S.XorClosed f) (ha : ¬Affine f) (hp : ¬Product f) :
    ∃g : G.Gadget n 2,G.Bad f g := by
  by_cases hm : S.MeetClosed f
  · obtain ⟨r,hr⟩ := R.exists_meet_closed f h0 hx hm ha hp
    exact ⟨G.ofRecipe r,G.ofRecipe_bad f r hr⟩
  · by_cases hw : W.CommonFourthSupport f
    · exact exists_sparse_phase f h0 hx hm ha hw
    · obtain ⟨r,hr⟩ := GeneralEOPairedFamilyExtractionSparseWeightRecipe.exists_recipe f h0 hx hm hw
      exact ⟨G.ofRecipe r,G.ofRecipe_bad f r hr⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionUniversal
