import Holant.Complexity.BinaryInterpolation.Chains.Network
import Holant.Proofs.Hardness.EOBinaryPlaneTract
import Holant.Marked.Monomial
import Holant.Proofs.Hardness.EONegativeWitness

/-! Actual binary centralization with a literal I vertex and native X edge.
The selected pairing class is preserved when the physical flip is undone. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBinaryEOCore
open Holant Holant.Tractable Holant.Marked
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace Ch
export Holant.Complexity.BinaryInterpolation.Chains
  (series binarySignature series_denote Uses Native series_uses series_native)
end Ch
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift (Compatible restrict class_lift)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option Elab.async false

/-- Port 0 is the free bit and port 1 its opposite. -/
def pairing : OrientedPerfectPairing 2 where
  count := 1
  ports := {
    toFun := fun p => if p.2 then 1 else 0
    invFun := fun i => (0,i=1)
    left_inv := by rintro ⟨j,b⟩; have hj : j=0 := Subsingleton.elim _ _; subst j; cases b <;> rfl
    right_inv := by intro i; fin_cases i <;> rfl }

theorem compatible (x : Fin 2→Bool) : L.Compatible pairing x ↔ x 0≠x 1 := by
  simp [L.Compatible,pairing]

theorem central_restrict (f : Signature AlgebraicComplex 2) (central : Signature.CentralSupport f) :
    L.restrict pairing f=f := by
  funext x
  by_cases hx : x 0≠x 1
  · simp [L.restrict,compatible,hx]
  · have same : x 0=x 1 := not_ne_iff.mp hx
    have zero : f x=0 := central x (by
      simp only [weight,Fin.sum_univ_two]
      rw [same]
      cases x 1 <;> decide)
    simp [L.restrict,compatible,hx,zero]

/-- One compressed pairing recovers the whole central binary in its SAME class. -/
theorem class_of_pairings (f : Signature AlgebraicComplex 2) (central : Signature.CentralSupport f)
    (C : EOClass) (pairings : EONegativeWitness.Pairings C ⟨2,f⟩) : C.Holds f := by
  rw [←central_restrict f central]
  exact L.class_lift pairing C (pairings pairing)

def flipWord (x : Fin 2→Bool) : Fin 2→Bool := ![x 0,!(x 1)]

theorem flipWord_involution (x : Fin 2→Bool) : flipWord (flipWord x)=x := by
  funext j
  fin_cases j <;> simp [flipWord]

theorem flipWord_affine : TwoTranslate.IsAffineMap flipWord := by
  intro x y
  funext j
  fin_cases j
  · change (x 0 ^^ y 0) = (x 0 ^^ (y 0 ^^ false))
    cases x 0 <;> cases y 0 <;> rfl
  · change (!(x 1 ^^ y 1)) = (!x 1 ^^ (!y 1 ^^ !false))
    cases x 1 <;> cases y 1 <;> rfl

theorem class_flip (f : Signature AlgebraicComplex 2) (C : EOClass) (h : C.Holds f) :
    C.Holds (fun x=>f (flipWord x)) := by
  cases C with
  | affine => exact h.precompose flipWord flipWord_affine
  | product =>
      have hp := EOBinaryPlaneTract.product_signed (fun j : Fin 2 => (j,j=1)) h
      have same : (fun x=>f (EOBinaryPlaneTract.signedMap (fun j : Fin 2 => (j,j=1)) x)) =
          (fun x=>f (flipWord x)) := by
        funext x
        apply congrArg f
        funext j
        fin_cases j <;> simp [flipWord,EOBinaryPlaneTract.signedMap]
      exact same ▸ hp

/-- Antidiagonal B is already EO. Diagonal B is joined to the actual I label. -/
def graph (B : Binary (K:=AlgebraicComplex)) (antidiagonal : Bool) : Network AlgebraicComplex 2 :=
  if antidiagonal then Network.corolla (Ch.binarySignature B)
  else Ch.series (Network.corolla (Ch.binarySignature B))
    (Network.corolla (Ch.binarySignature (Signature.equality : Binary (K:=AlgebraicComplex))))

def output (B : Binary (K:=AlgebraicComplex)) (antidiagonal : Bool) : Signature AlgebraicComplex 2 :=
  if antidiagonal then Ch.binarySignature B else fun x=>Ch.binarySignature B (flipWord x)

theorem graph_denote (B : Binary (K:=AlgebraicComplex)) (p : Bool) : (graph B p).denote=output B p := by
  cases p
  · change (Ch.series (Network.corolla (Ch.binarySignature B))
      (Network.corolla (Ch.binarySignature (Signature.equality : Binary (K:=AlgebraicComplex))))).denote = _
    rw [Ch.series_denote _ _ B Signature.equality
      (Network.denote_corolla _) (Network.denote_corolla _)]
    funext x
    cases h1 : x 1 <;> simp [output,Ch.binarySignature,flipWord,Matrix.mul_apply,X,Signature.disequality,
      Signature.equality,h1]
  · exact Network.denote_corolla _

theorem graph_native (B : Binary (K:=AlgebraicComplex)) (p : Bool) : Ch.Native (graph B p) := by
  cases p
  · exact Ch.series_native _ _ (fun e=>Fin.elim0 e) (fun e=>Fin.elim0 e)
  · exact fun e=>Fin.elim0 e

theorem graph_uses (B : Binary (K:=AlgebraicComplex)) (p : Bool) (F : SignatureFamily AlgebraicComplex)
    (hB : (⟨2,Ch.binarySignature B⟩ : AnySignature AlgebraicComplex)∈F)
    (hI : (⟨2,Ch.binarySignature (Signature.equality : Binary (K:=AlgebraicComplex))⟩ : AnySignature AlgebraicComplex)∈F) :
    Ch.Uses (graph B p) F := by
  cases p
  · exact Ch.series_uses _ _ F (fun _=>hB) (fun _=>hI)
  · exact fun _=>hB

theorem output_central (p : Bool) (w : Bool→Scalar) :
    Signature.CentralSupport (output (monomial p w) p) := by
  intro x hx
  change 2*weight x≠2 at hx
  simp only [weight,Fin.sum_univ_two] at hx
  cases p <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp_all [output,Ch.binarySignature,flipWord,monomial]

theorem output_nonzero (p : Bool) (w : Bool→Scalar) (live : ∀b,w b≠0) :
    output (monomial p w) p≠0 := by
  intro hz
  have h := congrFun hz ![false,true]
  cases p <;> simp [output,Ch.binarySignature,flipWord,monomial] at h
  all_goals exact live false h

/-- Undoing the actual flip preserves the selected affine or product class. -/
theorem class_reconstruct (B : Binary (K:=AlgebraicComplex)) (p : Bool) (C : EOClass)
    (h : C.Holds (output B p)) : C.Holds (Ch.binarySignature B) := by
  cases p
  · have lifted := class_flip (output B false) C h
    have exactUndo : (fun x=>output B false (flipWord x))=Ch.binarySignature B := by
      funext x
      exact congrArg (Ch.binarySignature B) (flipWord_involution x)
    exact exactUndo ▸ lifted
  · exact h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBinaryEOCore
end
