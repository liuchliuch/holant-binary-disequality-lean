import Holant.ReedMuller.SafeCollapse.Character
import Holant.ReedMuller.SafeCollapse.Physical

/-! Safe-group collapse, manuscript Lemma 7.13. Directions are the saturated
nonzero matrix representatives of actual finite-order transfers, so the result
is equality of the complete projective classes, not a finite sampled list. -/
namespace Holant.ReedMuller.SafeCollapse
open Holant Holant.ReedMuller.CoefficientAtlas
noncomputable section
set_option backward.isDefEq.respectTransparency false

def CompleteSafeDirections (F : SignatureFamily ℂ) : Set Mat :=
  {T | ∃ B : Mat,ActualSafeBinary F B ∧ ∃ c : ℂ,c≠0 ∧ T=c • transfer B}
def C2Directions : Set Mat :=
  {T | (∃ c : ℂ,c≠0 ∧ T=c • (Signature.equality : Mat)) ∨
       (∃ c : ℂ,c≠0 ∧ T=c • (Signature.disequality : Mat))}

theorem source_rm_safe_group_collapse (F : SignatureFamily ℂ) (q : Signature ℂ 8)
    (hI : (⟨2,binarySignature Signature.equality⟩ : AnySignature ℂ)∈F)
    (hs : SupportRM (walsh q))
    (hspan : Observability.linkedChainSpan (safeFamily F)=Observability.ixSpan)
    (hdeck : ∀ B,ActualSafeBinary F B → PhysicalDeck (onePort q (transfer B) 0)) :
    CompleteSafeDirections F=C2Directions := by
  have hbase := base_deck_of_safe_dressings F q hdeck
  ext T
  constructor
  · rintro ⟨B,hB,c,hc,rfl⟩
    have hd : det (transfer B)≠0 := by rw [det_transfer];exact neg_ne_zero.mpr hB.2.1
    have hh := proper_safe_transfer_collapse q hs hbase (transfer B)
      (proper_safe_transfer F hspan B hB) hd 0 (hdeck B hB)
    rcases hh with ⟨d,hd,hT⟩ | ⟨d,hd,hT⟩
    · left
      refine ⟨c*d,mul_ne_zero hc hd,?_⟩
      rw [hT]
      funext a b
      simp [Pi.smul_apply,smul_eq_mul,mul_assoc]
    · right
      refine ⟨c*d,mul_ne_zero hc hd,?_⟩
      rw [hT]
      funext a b
      simp [Pi.smul_apply,smul_eq_mul,mul_assoc]
  · rintro (⟨c,hc,rfl⟩|⟨c,hc,rfl⟩)
    · refine ⟨Signature.disequality,safe_native_X F,c,hc,?_⟩
      simp [transfer]
    · refine ⟨Signature.equality,safe_literal_I F hI,c,hc,?_⟩
      simp [transfer]

/-- Fixed actual representative tables have exactly the same proper-span
condition as all actual safe binaries, using the source's recorded scalars. -/
structure FixedSafeRepresentatives (F : SignatureFamily ℂ) {ι : Type*} (B : ι → Mat) : Prop where
  actual : ∀ i,ActualSafeBinary F (B i)
  complete : ∀ C,ActualSafeBinary F C → ∃ i,∃ c : ℂ,c≠0 ∧ C=c • B i

theorem proper_span_of_fixed_representatives (F : SignatureFamily ℂ) {ι : Type*} (B : ι → Mat)
    (hB : FixedSafeRepresentatives F B) (hspan : Observability.linkedChainSpan B=Observability.ixSpan) :
    Observability.linkedChainSpan (safeFamily F)=Observability.ixSpan := by
  rw [Observability.linkedChainSpan_eq] at hspan ⊢
  apply (Observability.chainSpan_eq_ixSpan_iff _).mpr
  intro C
  obtain ⟨i,c,hc,hC⟩ := hB.complete C.val C.property
  change C.val∈Observability.ixSpan
  rw [hC]
  exact Observability.ixSpan.smul_mem c ((Observability.chainSpan_eq_ixSpan_iff _).mp hspan i)

/-- The source fixed-representative specialization. Only first-port dressings
are needed; a standing deck hypothesis on every safe dressing implies this one. -/
theorem source_rm_safe_group_collapse_from_representatives
    (F : SignatureFamily ℂ) (q : Signature ℂ 8) {ι : Type*} (B : ι → Mat)
    (hB : FixedSafeRepresentatives F B)
    (hI : (⟨2,binarySignature Signature.equality⟩ : AnySignature ℂ)∈F)
    (hs : SupportRM (walsh q)) (hspan : Observability.linkedChainSpan B=Observability.ixSpan)
    (hdeck : ∀ C,ActualSafeBinary F C → PhysicalDeck (onePort q (transfer C) 0)) :
    CompleteSafeDirections F=C2Directions :=
  source_rm_safe_group_collapse F q hI hs (proper_span_of_fixed_representatives F B hB hspan) hdeck

/-- The two surviving projective classes are distinct. -/
theorem identity_not_exchange_direction :
    ¬∃ c : ℂ,c≠0 ∧ (Signature.equality : Mat)=c • Signature.disequality := by
  rintro ⟨c,hc,h⟩
  have H := congrFun (congrFun h false) false
  simp [Signature.equality,Signature.disequality] at H

/-- Every displayed first-port transfer operation is an actual gadget over the
same retained family whenever its core is retained. -/
theorem safe_dressing_actual (F : SignatureFamily ℂ) (q : Signature ℂ 8)
    (hq : (⟨8,q⟩ : AnySignature ℂ)∈F) (B : Mat) (hB : ActualSafeBinary F B) :
    Gadget.Realizes F .disequality (onePort q (transfer B) 0) :=
  realizes_onePort F q B (Gadget.realizes_of_mem F .disequality q hq) hB.1

end
end Holant.ReedMuller.SafeCollapse
