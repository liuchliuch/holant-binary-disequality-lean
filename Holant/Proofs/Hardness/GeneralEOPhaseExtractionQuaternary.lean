import Holant.Proofs.Hardness.GeneralEOPhaseExtractionSigns
import Holant.Proofs.Hardness.EOBinaryPlaneClassification
import Holant.Proofs.Hardness.EOBinaryPlaneCore

/-! The signed phase endpoint is either dense or a full
opposite-pair plane with nonproduct binary compression. Compression here is
only a coefficient formula; it is never installed as a free physical vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionQuaternary
open Holant Holant.Tractable
namespace C
export GeneralEOPhaseExtractionCore (Collinear area noncollinear_nonzero)
end C
namespace I
abbrev Phase {n : ℕ} (f : Signature ℂ n) : Prop := ∃x y,¬C.Collinear (f x) (f y)
end I
namespace S
export GeneralEOPhaseExtractionSigns (Sign)
end S
namespace R
export GeneralEOPhaseExtractionStructure (SinglePhase)
end R
namespace F
export SelfDualPinObstruction (flip)
end F
namespace B
export EOBinaryPlaneCore (word compress lift compress_lift normalized normalized_lift)
end B
namespace O
export FiveSupportEOOrdering (middleWord middleCoeff orderAt)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem flip_two (u v : Bool) : F.flip (![u,v] : Fin 2 → Bool)=![!u,!v] := by
  funext i
  fin_cases i <;> rfl

theorem binary_relations (f : Signature ℂ 2) (hS : S.Sign f) :
    (f ![true,true]=f ![false,false] ∧ f ![true,false]=f ![false,true]) ∨
    (f ![true,true]= -f ![false,false] ∧ f ![true,false]= -f ![false,true]) := by
  rcases hS with hS|hS
  · exact Or.inl ⟨by simpa only [flip_two,Bool.not_false] using hS ![false,false],
      by simpa only [flip_two,Bool.not_false,Bool.not_true] using hS ![false,true]⟩
  · exact Or.inr ⟨by simpa only [flip_two,Bool.not_false] using hS ![false,false],
      by simpa only [flip_two,Bool.not_false,Bool.not_true] using hS ![false,true]⟩

theorem binary_singlePhase_of_collinear (f : Signature ℂ 2) (hS : S.Sign f)
    (hab : C.Collinear (f ![false,false]) (f ![false,true])) : R.SinglePhase f := by
  have words (x : Fin 2 → Bool) : x=![x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  intro x y
  rw [words x,words y]
  rcases binary_relations f hS with ⟨h11,h10⟩|⟨h11,h10⟩
  all_goals
    cases x 0 <;> cases x 1 <;> cases y 0 <;> cases y 1
    all_goals
      simp only [h11,h10,C.Collinear,C.area,Complex.neg_re,Complex.neg_im] at hab ⊢
      nlinarith [hab]

theorem binary_phase_pair (f : Signature ℂ 2) (hS : S.Sign f) (hP : I.Phase f) :
    ¬C.Collinear (f ![false,false]) (f ![false,true]) := by
  intro h
  obtain ⟨x,y,hxy⟩ := hP
  exact hxy (binary_singlePhase_of_collinear f hS h x y)

theorem binary_full (f : Signature ℂ 2) (hS : S.Sign f) (hP : I.Phase f) : ∀x,f x≠0 := by
  obtain ⟨ha,hb⟩ := C.noncollinear_nonzero (binary_phase_pair f hS hP)
  have words (x : Fin 2 → Bool) : x=![x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  intro x
  rw [words x]
  rcases binary_relations f hS with ⟨h11,h10⟩|⟨h11,h10⟩
  all_goals
    cases x 0 <;> cases x 1
    all_goals first | exact ha | exact hb | simpa [h11,h10] using ha | simpa [h11,h10] using hb

theorem collinear_of_sq_eq (a b : ℂ) (h : a^2=b^2) : C.Collinear a b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h|h
  · rw [h]
    simp [C.Collinear,C.area,mul_comm]
  · rw [h]
    unfold C.Collinear C.area
    simp only [Complex.neg_re,Complex.neg_im]
    ring

theorem binary_nonCross (f : Signature ℂ 2) (hS : S.Sign f) (hP : I.Phase f) :
    f ![false,false]*f ![true,true]≠f ![false,true]*f ![true,false] := by
  intro hc
  apply binary_phase_pair f hS hP
  apply collinear_of_sq_eq
  rcases binary_relations f hS with ⟨h11,h10⟩|⟨h11,h10⟩
  · rw [h11,h10] at hc
    linear_combination hc
  · rw [h11,h10] at hc
    linear_combination -hc

theorem phase_of_lift (f : Signature ℂ 2) (hP : I.Phase (B.lift f)) : I.Phase f := by
  obtain ⟨x,y,hxy⟩ := hP
  obtain ⟨hx,hy⟩ := C.noncollinear_nonzero hxy
  have hxc : x 1=!(x 0) ∧ x 3=!(x 2) := by
    by_contra h
    exact hx (by simp [B.lift,h])
  have hyc : y 1=!(y 0) ∧ y 3=!(y 2) := by
    by_contra h
    exact hy (by simp [B.lift,h])
  exact ⟨![x 0,x 2],![y 0,y 2],by simpa [B.lift,hxc,hyc] using hxy⟩

theorem sign_of_lift (f : Signature ℂ 2) (hS : S.Sign (B.lift f)) : S.Sign f := by
  have hv (z : Fin 2 → Bool) : B.lift f (B.word z)=f z := congrFun (B.compress_lift f) z
  have hf (z : Fin 2 → Bool) : F.flip (B.word z)=B.word (F.flip z) := by
    funext i
    fin_cases i <;> rfl
  rcases hS with hS|hS
  · left
    intro z
    have h := hS (B.word z)
    rwa [hf,hv,hv] at h
  · right
    intro z
    have h := hS (B.word z)
    rwa [hf,hv,hv] at h

theorem phase_reindex {n : ℕ} (f : Signature ℂ n) (e : Equiv.Perm (Fin n))
    (hP : I.Phase f) : I.Phase (Tensor.reindex e f) := by
  obtain ⟨x,y,hxy⟩ := hP
  refine ⟨x ∘ e.symm,y ∘ e.symm,?_⟩
  have hv (z : Fin n → Bool) : Tensor.reindex e f (z ∘ e.symm)=f z := by
    apply congrArg f
    funext i
    simp [Function.comp_apply]
  simpa only [hv] using hxy

theorem sign_reindex {n : ℕ} (f : Signature ℂ n) (e : Equiv.Perm (Fin n))
    (hS : S.Sign f) : S.Sign (Tensor.reindex e f) := by
  rcases hS with hS|hS
  · exact Or.inl (fun x => hS (x ∘ e))
  · exact Or.inr (fun x => hS (x ∘ e))

def image {n : ℕ} (f : Signature AlgebraicComplex n) : Signature ℂ n := fun x => f x

theorem algebraic_binary_full_nonproduct (f : Signature AlgebraicComplex 2)
    (hS : S.Sign (image f)) (hP : I.Phase (image f)) :
    EOBinaryPlaneClassification.Full f ∧ ¬Product f := by
  have hfull : EOBinaryPlaneClassification.Full f := by
    intro x hx
    exact binary_full (image f) hS hP x (congrArg Subtype.val hx)
  refine ⟨hfull,?_⟩
  intro hp
  have hc := (EOBinaryPlaneClassification.full_product_iff f hfull).mp hp
  exact binary_nonCross (image f) hS hP (congrArg Subtype.val hc)

theorem flip_middle (i : Fin 6) : F.flip (O.middleWord i)=O.middleWord (5-i) := by
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem opposite_zero (M : Signature AlgebraicComplex 4) (hS : S.Sign (image M))
    (i : Fin 6) (h0 : O.middleCoeff M i=0) : O.middleCoeff M (5-i)=0 := by
  apply Subtype.ext
  have hc : image M (O.middleWord i)=0 := congrArg Subtype.val h0
  rcases hS with hS|hS
  · have h := hS (O.middleWord i)
    rw [flip_middle,hc] at h
    exact h
  · have h := hS (O.middleWord i)
    rw [flip_middle,hc,neg_zero] at h
    exact h

/-- Given a missing middle entry, the actual original port order is fixed by
that entry. Phase and the complement sign force the remaining plane to be full
and nonproduct; no class membership premise is assumed. -/
theorem plane_of_zero (M : Signature AlgebraicComplex 4)
    (hE : Signature.CentralSupport M) (hS : S.Sign (image M)) (hP : I.Phase (image M))
    (i : Fin 6) (h0 : O.middleCoeff M i=0) :
    let e := O.orderAt i
    let f := B.compress (Tensor.reindex e M)
    Tensor.reindex e M=B.lift f ∧ EOBinaryPlaneClassification.Full f ∧ ¬Product f := by
  dsimp only
  have he : DenseEOUnitLocal.EOSupport M := by
    intro x hx
    apply hE
    omega
  have h1 := opposite_zero M hS i h0
  have hl : B.normalized M i=B.lift (B.compress (B.normalized M i)) :=
    (B.normalized_lift M he i h0 h1).symm
  refine ⟨hl,?_⟩
  have hlc : Tensor.reindex (O.orderAt i) (image M)=
      B.lift (image (B.compress (B.normalized M i))) := by
    funext x
    change ((B.normalized M i x : AlgebraicComplex) : ℂ)=_
    rw [congrFun hl x]
    by_cases hc : x 1=!(x 0) ∧ x 3=!(x 2) <;> simp [B.lift,image,hc]
  have hs := sign_reindex (image M) (O.orderAt i) hS
  have hp := phase_reindex (image M) (O.orderAt i) hP
  rw [hlc] at hs hp
  exact algebraic_binary_full_nonproduct _ (sign_of_lift _ hs) (phase_of_lift _ hp)

theorem dense_of_middle (M : Signature AlgebraicComplex 4)
    (h : ∀i : Fin 6,O.middleCoeff M i≠0) : ∀x,weight x=2 → M x≠0 := by
  intro x hx
  have hsum := hx
  simp only [weight,Fin.sum_univ_four] at hsum
  have hw : x=![x 0,x 1,x 2,x 3] := by funext i; fin_cases i <;> rfl
  rw [hw]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals first
    | exact h 0 | exact h 1 | exact h 2 | exact h 3 | exact h 4 | exact h 5
    | norm_num [h0,h1,h2,h3] at hsum

theorem dense_or_full_nonproduct_plane (M : Signature AlgebraicComplex 4)
    (hE : Signature.CentralSupport M) (hS : S.Sign (image M)) (hP : I.Phase (image M)) :
    (∀x,weight x=2 → M x≠0) ∨
    ∃e : Equiv.Perm (Fin 4),
      Tensor.reindex e M=B.lift (B.compress (Tensor.reindex e M)) ∧
      EOBinaryPlaneClassification.Full (B.compress (Tensor.reindex e M)) ∧
      ¬Product (B.compress (Tensor.reindex e M)) := by
  classical
  by_cases hd : ∀i : Fin 6,O.middleCoeff M i≠0
  · exact Or.inl (dense_of_middle M hd)
  · push Not at hd
    obtain ⟨i,hi⟩ := hd
    exact Or.inr ⟨O.orderAt i,plane_of_zero M hE hS hP i hi⟩

/-- Pairing restriction is used only to refute the literal tractability
criterion. This theorem does not assert realization of a restriction. -/
theorem nontract_of_nonaffine_plane (M : Signature AlgebraicComplex 4)
    (e : Equiv.Perm (Fin 4)) (f : Signature AlgebraicComplex 2)
    (hplane : Tensor.reindex e M=B.lift f) (hA : ¬Affine f) (hP : ¬Product f) :
    ¬EOTract {⟨4,M⟩} := by
  rintro ⟨_,_,sign,cl,hs,hc⟩
  have h := hc ⟨4,M⟩ (by simp)
    (EOBinaryPlaneTract.transportPairing e EOBinaryPlaneCore.pairing)
  rw [EOBinaryPlaneTract.restriction_reindex,hplane,EOBinaryPlaneCore.restrict_eq,
    B.compress_lift] at h
  cases cl
  · exact hA h
  · exact hP h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionQuaternary
