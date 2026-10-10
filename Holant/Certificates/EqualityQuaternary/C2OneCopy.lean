import Holant.Certificates.EqualityQuaternary.C2PhysicalDeck
import Holant.Certificates.EqualityQuaternary.MonomialSource

/-! The complete one-copy clause of A.8(i). Physical safety first derives
the odd-coordinate zeros and the block equations. The sign hypothesis here
is exactly the source's endpoint/common-active-sign case distinction.
The mixed-sign two-copy exit is not asserted in this file.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.C2
open Holant Holant.Marked Holant.Tractable
open Holant.Projective.CyclicQuaternary
open Holant.Projective.CyclicQuaternary.Physical hiding Scalar Mat
open Holant.Marked.SupportAtlas (parity complement xorWord parity_xorWord)
open Holant.EightVertex.ProductAnchor (EndpointEven)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def CommonActiveSigns (a : Signature Scalar 4) : Prop :=
  ∃ eps : Scalar, (eps=1 ∨ eps = -1) ∧ ∀ i : Fin 3,
    (coordinates a i).1 ≠ 0 → (coordinates a i).2/(coordinates a i).1=eps

def OneCopyCase (q : Signature Scalar 4) : Prop :=
  endpoint0 (walsh q) ≠ 0 ∨ CommonActiveSigns (walsh q)

theorem uniform_sign (a : Signature Scalar 4) (hs : ∀ i,
    SafeBlock (endpoint0 a) (endpoint1 a) (coordinates a i).1 (coordinates a i).2)
    (hcase : endpoint0 a ≠ 0 ∨ CommonActiveSigns a) :
    ∃ b : Bool, endpoint1 a=sign b*endpoint0 a ∧
      ∀ i, (coordinates a i).2=sign b*(coordinates a i).1 := by
  have hex : ∃ eps : Scalar, (eps=1 ∨ eps = -1) ∧ endpoint1 a=eps*endpoint0 a ∧
      ∀ i, (coordinates a i).2=eps*(coordinates a i).1 := by
    by_cases hu : endpoint0 a=0
    · have hv : endpoint1 a=0 := (endpoints_zero_iff (hs 0)).mp hu
      obtain ⟨eps,heps,hactive⟩ := hcase.resolve_left (not_not.mpr hu)
      refine ⟨eps,heps,by rw [hu,hv,mul_zero],?_⟩
      intro i
      by_cases hx : (coordinates a i).1=0
      · rw [hx,(active_zero_iff (hs i)).mp hx,mul_zero]
      · exact (div_eq_iff hx).mp (hactive i hx)
    · exact common_sign_of_endpoint _ _ (fun i => (coordinates a i).1)
        (fun i => (coordinates a i).2) hu hs
  obtain ⟨eps,heps,hv,hxy⟩ := hex
  rcases heps with rfl | rfl
  · exact ⟨false,hv,hxy⟩
  · exact ⟨true,hv,hxy⟩

def commonTable (b : Bool) (u : Scalar) (x : Fin 3 → Scalar) : Signature Scalar 4 :=
  ofCoordinates u (sign b*u) (fun i => (x i,sign b*x i))

def inverseCommon (b : Bool) (u : Scalar) (x : Fin 3 → Scalar) : Signature Scalar 4 :=
  Signature.coordinateAction (fun _ => P) (commonTable b u x)

theorem inverseCommon_complement (b : Bool) (u : Scalar) (x : Fin 3 → Scalar)
    (w : Fin 4 → Bool) : inverseCommon b u x (complement w)=inverseCommon b u x w := by
  cases b <;> cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [inverseCommon,commonTable,Signature.coordinateAction,sum_words4,
      Fin.prod_univ_succ,P,ofCoordinates,complement,sign,h0,h1,h2,h3] <;> ring

theorem inverseCommon_parity (b : Bool) (u : Scalar) (x : Fin 3 → Scalar)
    (w : Fin 4 → Bool) (hw : parity w ≠ b) : inverseCommon b u x w=0 := by
  cases b <;> cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [parity,h0,h1,h2,h3] at hw
  all_goals
    simp [inverseCommon,commonTable,Signature.coordinateAction,sum_words4,
      Fin.prod_univ_succ,P,ofCoordinates,sign,h0,h1,h2,h3] <;> ring

/-- Fourier inversion is proved as an inverse action on the actual original q. -/
theorem common_form (q : Signature Scalar 4) (he : EvenSupported (walsh q)) (b : Bool)
    (hv : endpoint1 (walsh q)=sign b*endpoint0 (walsh q))
    (hxy : ∀ i, (coordinates (walsh q) i).2=sign b*(coordinates (walsh q) i).1) :
    q=inverseCommon b (endpoint0 (walsh q)) (fun i => (coordinates (walsh q) i).1) := by
  have hcoords : coordinates (walsh q) = fun i =>
      ((coordinates (walsh q) i).1,sign b*(coordinates (walsh q) i).1) := by
    funext i
    exact Prod.ext rfl (hxy i)
  have ht : commonTable b (endpoint0 (walsh q)) (fun i => (coordinates (walsh q) i).1)=walsh q := by
    unfold commonTable
    rw [←hv,←hcoords]
    exact ofCoordinates_extract _ he
  have hinv : Signature.coordinateAction (fun _ => P) (walsh q)=q :=
    Signature.coordinateAction_cancel _ _ (fun _ => P_Pinv) q
  rw [inverseCommon,ht,hinv]

theorem source_C2_one_copy_support {F : SignatureFamily Scalar} (reps : Representatives F)
    (q : Signature Scalar 4) (hdeck : PhysicalDeck reps q) (hcase : OneCopyCase q) :
    ∃ b : Bool, (∀ w, parity w ≠ b → q w=0) ∧ ∀ w, q (complement w)=q w := by
  have hs := physical_walshSafe reps q hdeck
  obtain ⟨b,hv,hxy⟩ := uniform_sign (walsh q) (safe_blocks _ hs) hcase
  have he := common_form q (odd_coefficients_zero _ hs) b hv hxy
  refine ⟨b,?_,?_⟩
  · intro w hw
    rw [he]
    exact inverseCommon_parity b _ _ w hw
  · intro w
    rw [he]
    exact inverseCommon_complement b _ _ w

theorem source_C2_one_copy_endpoint {F : SignatureFamily Scalar} (reps : Representatives F)
    (q : Signature Scalar 4) (hq : q≠0) (hdeck : PhysicalDeck reps q) (hcase : OneCopyCase q) :
    ∃ mask : Fin 4 → Bool, EndpointEven (Flip.value q mask) := by
  obtain ⟨b,hpar,hcomp⟩ := source_C2_one_copy_support reps q hdeck hcase
  obtain ⟨mask,hmask⟩ : ∃ mask,q mask≠0 := by
    by_contra hh
    push Not at hh
    exact hq (funext hh)
  have hpm : parity mask=b := by
    by_contra hh
    exact hmask (hpar mask hh)
  refine ⟨mask,?_,?_,?_⟩
  · simpa [Flip.value,xorWord] using hmask
  · simpa [Flip.value,xorWord,complement,hcomp] using hmask
  · intro w hw
    change q (xorWord w mask)=0
    apply hpar
    rw [parity_xorWord,(parity_weight w).mpr hw,hpm]
    cases b <;> decide

/-- The source one-copy C2 clause has the same literal one-q native network
and prime/nonmatching conclusion as the monomial row. -/
theorem source_C2_one_copy_boundary {F : SignatureFamily Scalar} (reps : Representatives F)
    (q : Signature Scalar 4) (hq : TensorPrime q)
    (hqActual : Gadget.Realizes F .disequality q)
    (hI : Gadget.Realizes F .disequality (kernelSignature Signature.equality))
    (hdeck : PhysicalDeck reps q) (hcase : OneCopyCase q) :
    ∃ mask : Fin 4 → Bool, EndpointEven (Flip.value q mask) ∧
      TensorPrime (Flip.value q mask) ∧ ¬GroupMatching {B | ∃ p c, c≠0 ∧ B=scale c (binary p)}
        (Flip.value q mask) ∧ Gadget.Realizes F .disequality (Flip.value q mask) ∧
      (Flip.network q mask).denote=Flip.value q mask ∧
      (Finset.univ.filter (fun v : Fin (Flip.network q mask).shape.vertices =>
        (Flip.network q mask).shape.arity v=4)).card=1 := by
  classical
  obtain ⟨mask,he⟩ := source_C2_one_copy_endpoint reps q hq.1 hdeck hcase
  have hp := flip_prime hq mask
  exact ⟨mask,he,hp,prime_not_matching hp,Flip.actual F q hqActual hI mask,
    Flip.denote q mask,Flip.quaternary_count q mask⟩

end Holant.Certificates.EqualityQuaternary.C2
