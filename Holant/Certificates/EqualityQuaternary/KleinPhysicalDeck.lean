import Holant.Certificates.EqualityQuaternary.KleinPermutation

/-! Physical-source bridge for both Klein rows. All actual representative
scalars, all port orders, and zero cards are retained. Frobenius duals are
derived scalar multiples of the original group directions.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
set_option backward.isDefEq.respectTransparency false

structure Representatives (F : SignatureFamily Scalar) (kind : Kind) where
  matrix : Fin 4 → Mat
  multiplier : Fin 4 → Scalar
  multiplier_ne_zero : ∀ k,multiplier k≠0
  actual : ∀ k,Gadget.Realizes F .disequality (kernelSignature (matrix k))
  normal_form : ∀ k,matrix k=scale (multiplier k) (E kind k)

def PhysicalDeck {F : SignatureFamily Scalar} {kind : Kind} (reps : Representatives F kind)
    (q : Signature Scalar 4) : Prop :=
  ∀ (e : Equiv.Perm (Fin 4)) (k : Fin 4),physicalCard q e (reps.matrix k)=0 ∨
    ∃ j c,c≠0 ∧ physicalCard q e (reps.matrix k)=scale c (reps.matrix j)

def AllStandardCards (kind : Kind) (q : Signature Scalar 4) : Prop :=
  ∀ (e : Equiv.Perm (Fin 4)) (k : Fin 4),OnLine kind (contract0 (reorder q e) (E kind k))

theorem OnLine.scale {kind : Kind} {B : Mat} (h : OnLine kind B) (c : Scalar) : OnLine kind (scale c B) := by
  obtain ⟨k,d,rfl⟩ := h
  exact ⟨k,c*d,by funext a b; exact (mul_assoc c d (E kind k a b)).symm⟩

theorem onLine_scale_iff (kind : Kind) (c : Scalar) (hc : c≠0) (B : Mat) :
    OnLine kind (scale c B) ↔ OnLine kind B := by
  constructor
  · intro h
    have hh := h.scale c⁻¹
    have he : scale c⁻¹ (scale c B)=B := by funext a b; simp [scale,hc]
    rwa [he] at hh
  · exact fun h => h.scale c

def closingSign (k : Fin 4) : Scalar := if k=0 ∨ k=1 then 1 else -1
def closingSignQ (k : Fin 4) : Q := if k=0 ∨ k=1 then 1 else -1

theorem closing_Q : ∀ kind k a b,
    basisQ kind k (!a) (!b)=closingSignQ k*basisQ kind k a b := by
  intro kind k a b
  cases kind <;> fin_cases k <;> cases a <;> cases b <;> decide +kernel

theorem closing (kind : Kind) (k : Fin 4) :
    Kernel.mul (Kernel.mul Signature.disequality (E kind k)) Signature.disequality=
      scale (closingSign k) (E kind k) := by
  funext a b
  rw [Kernel.disequality_sandwich]
  have h := congrArg embed (closing_Q kind k a b)
  by_cases hk : k=0 ∨ k=1 <;> simpa [E,scale,closingSignQ,closingSign,hk] using h

theorem closingSign_ne_zero (k : Fin 4) : closingSign k≠0 := by
  unfold closingSign
  split_ifs <;> norm_num

theorem physical_normalization {F : SignatureFamily Scalar} {kind : Kind}
    (reps : Representatives F kind) (q : Signature Scalar 4) (e : Equiv.Perm (Fin 4)) (k : Fin 4) :
    physicalCard q e (reps.matrix k)=scale (reps.multiplier k*closingSign k)
      (contract0 (reorder q e) (E kind k)) := by
  rw [physicalCard,reps.normal_form,scale_mul_right,scale_mul_left,closing,
    contract0_scale,contract0_scale]
  funext a b
  simp [scale,mul_assoc]

theorem standardCards_of_physical {F : SignatureFamily Scalar} {kind : Kind}
    (reps : Representatives F kind) (q : Signature Scalar 4) (h : PhysicalDeck reps q) :
    AllStandardCards kind q := by
  intro e k
  have hs : OnLine kind (physicalCard q e (reps.matrix k)) := by
    rcases h e k with hz | ⟨j,c,_,he⟩
    · exact ⟨0,0,by rw [hz]; funext a b; simp [scale]⟩
    · rw [he,reps.normal_form]
      exact (OnLine.scale ⟨j,1,by funext a b; simp [scale]⟩ (reps.multiplier j)).scale c
  rw [physical_normalization] at hs
  exact (onLine_scale_iff kind _ (mul_ne_zero (reps.multiplier_ne_zero k) (closingSign_ne_zero k)) _).mp hs

def theta (kind : Kind) (k : Fin 4) : Fin 4 :=
  match kind with | .standard => k | .exotic => ![0,1,3,2] k
def dualScalarQ (kind : Kind) (k : Fin 4) : Q :=
  match kind with | .standard => qHalf | .exotic => if k=0 ∨ k=1 then qHalf else qQuarter

theorem dual_scalar_Q : ∀ kind k a b,
    dualQ kind k a b=dualScalarQ kind k*basisQ kind (theta kind k) a b := by
  intro kind k a b
  cases kind <;> fin_cases k <;> cases a <;> cases b <;> decide +kernel

theorem dual_scalar (kind : Kind) (k : Fin 4) :
    dual kind k=scale (embed (dualScalarQ kind k)) (E kind (theta kind k)) := by
  funext a b
  have h := congrArg embed (dual_scalar_Q kind k a b)
  simpa [dual,E,scale] using h

theorem dualCards_of_standard {kind : Kind} {q : Signature Scalar 4}
    (h : AllStandardCards kind q) : AllDualCards kind q := by
  intro e k
  rw [card,dual_scalar,contract0_scale]
  exact (h e (theta kind k)).scale _

theorem source_klein_permutation {F : SignatureFamily Scalar} {kind : Kind}
    (reps : Representatives F kind) (q : Signature Scalar 4) (h : PhysicalDeck reps q) :
    ∃ (p : Equiv.Perm (Fin 4)) (c : Fin 4 → Scalar),q=normalized kind p c :=
  source_permutation_form (dualCards_of_standard (standardCards_of_physical reps q h))

end Holant.Certificates.EqualityQuaternary.Klein
