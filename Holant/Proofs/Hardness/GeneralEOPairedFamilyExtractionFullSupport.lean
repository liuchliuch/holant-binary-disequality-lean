import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionCoordinates
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionTensor
import Holant.Proofs.Hardness.EOBinaryPlaneProduct

/-! Generic arbitrary-arity full-support interaction extraction. Vanishing of
all actual two-coordinate face determinants reconstructs a literal Product
formula. Hence nonproduct full support internally supplies a nonproduct binary
restriction; no caller-selected minor or hard gadget is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionFullSupport
open Holant Holant.Tractable
open Function
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false


variable {n : ℕ}

def face (f : Signature AlgebraicComplex n) (i j : Fin n) (x : Fin n → Bool) :
    Signature AlgebraicComplex 2 := fun z => f (update (update x i (z 0)) j (z 1))

def RankOneFaces (f : Signature AlgebraicComplex n) : Prop :=
  ∀i j,i≠j → ∀x,EOBinaryPlaneClassification.Cross (face f i j x)

theorem face_full (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0)
    (i j : Fin n) (x : Fin n → Bool) : EOBinaryPlaneClassification.Full (face f i j x) := fun _ => hf _

theorem rankOne_pin {f : Signature AlgebraicComplex (n+1)} (h : RankOneFaces f) (b : Bool) :
    RankOneFaces (fun x : Fin n → Bool => f (Fin.cons b x)) := by
  intro i j hij x
  have hh := h i.succ j.succ (fun he => hij (Fin.succ_injective _ he)) (Fin.cons b x)
  simpa only [EOBinaryPlaneClassification.Cross,face,Fin.cons_update] using hh

theorem ratio_constant {f : Signature AlgebraicComplex (n+1)} (hf : ∀x,f x≠0)
    (h : RankOneFaces f) (x y : Fin n → Bool) :
    f (Fin.cons true x)/f (Fin.cons false x)=f (Fin.cons true y)/f (Fin.cons false y) := by
  apply constant_of_coordinates n (fun z => f (Fin.cons true z)/f (Fin.cons false z)) _ x y
  intro j z
  have hh := h 0 j.succ (Ne.symm (Fin.succ_ne_zero j)) (Fin.cons false z)
  simp only [EOBinaryPlaneClassification.Cross, face, Fin.update_cons_zero, ←Fin.cons_update] at hh
  change f (Fin.cons false (update z j false))*f (Fin.cons true (update z j true))=
    f (Fin.cons false (update z j true))*f (Fin.cons true (update z j false)) at hh
  apply (div_eq_div_iff (hf _) (hf _)).mpr
  linear_combination -hh

/-- Construct Product recursively, including the nullary case. Full support
is essential: sparse linear codes need a separate support extraction. -/
theorem product_of_rankOneFaces : ∀n : ℕ, ∀f : Signature AlgebraicComplex n,
    (∀x,f x≠0) → RankOneFaces f → Product f := by
  intro n
  induction n with
  | zero =>
    intro f hf h
    have he : f=(fun _ => f Fin.elim0) := funext fun x => congrArg f (Subsingleton.elim _ _)
    rw [he]
    exact product_constant 0 _
  | succ n ih =>
    intro f hf h
    let lower : Signature AlgebraicComplex n := fun x => f (Fin.cons false x)
    let origin : Fin n → Bool := fun _ => false
    let c : AlgebraicComplex := f (Fin.cons true origin)/f (Fin.cons false origin)
    have hl : Product lower := ih lower (fun x => hf _) (rankOne_pin h false)
    have hr (x : Fin n → Bool) : f (Fin.cons true x)=c*lower x := by
      have hh := ratio_constant hf h x origin
      exact (div_eq_iff (hf _)).mp hh
    have hp : Product (fun x : Fin (n+1) → Bool => lower (Fin.tail x)) :=
      GeneralEOPairedFamilyExtractionTensor.product_substitute (fun i => Sum.inr i.succ) hl
    have hu : Product (fun x : Fin (n+1) → Bool => if x 0 then c else 1) :=
      product_unary 0 (fun b => if b then c else 1)
    have he : f=(fun x : Fin (n+1) → Bool => (if x 0 then c else 1)*lower (Fin.tail x)) := by
      funext x
      have hh := Fin.cons_self_tail x
      cases hb : x 0 with
      | false =>
        have hx : Fin.cons false (Fin.tail x)=x := by simpa only [hb] using hh
        simp only [Bool.false_eq_true, ↓reduceIte, one_mul, lower, hx]
      | true =>
        have hx : Fin.cons true (Fin.tail x)=x := by simpa only [hb] using hh
        simpa only [hb, ↓reduceIte, hx] using hr (Fin.tail x)
    rw [he]
    exact hu.mul hp

/-- The interaction is extracted from an arbitrary original full-support row;
the selected two coordinates, their order, and every fixed bit are retained. -/
theorem exists_nonproduct_face (f : Signature AlgebraicComplex n)
    (hf : ∀x,f x≠0) (hp : ¬Product f) :
    ∃i j : Fin n, i≠j ∧ ∃x : Fin n → Bool,
      EOBinaryPlaneClassification.Full (face f i j x) ∧ ¬Product (face f i j x) := by
  have hh : ¬RankOneFaces f := fun h => hp (product_of_rankOneFaces n f hf h)
  unfold RankOneFaces at hh
  obtain ⟨i,hi⟩ := not_forall.mp hh
  obtain ⟨j,hj⟩ := not_forall.mp hi
  have hij : i≠j := by by_contra he; exact hj (fun hn => False.elim (hn he))
  obtain ⟨x,hx⟩ := not_forall.mp (fun ht => hj (fun _ => ht))
  refine ⟨i,j,hij,x,face_full f hf i j x,?_⟩
  exact fun h => hx ((EOBinaryPlaneClassification.full_product_iff _ (face_full f hf i j x)).mp h)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionFullSupport
