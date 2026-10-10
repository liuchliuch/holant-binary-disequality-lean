import Holant.Proofs.Hardness.GeneralEOSignedNativeNormalization
import Holant.Complexity.EncodedHolantOutputSize

/-! The typed parity normalization specializes to the literal validated raw
network and its original finite row dictionary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeDecoded
open Holant Holant.Tractable Holant.Complexity
open scoped BigOperators
namespace N
export GeneralEOSignedNativeParity (port links signedInput signed_sum inconsistent_denote)
end N
namespace D
export GeneralEOSignedParityComponents (Good scope)
end D
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable {s : ℕ} {arity : ℕ → ℕ}
abbrev Input := ExactSignatureTables.Input s 1 arity

def label (r : Input (s:=s) (arity:=arity)) (v : Fin r.val.vertices.length) : Fin s :=
  r.val.signatureLabel r.property v

def pairing (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
    (r : Input (s:=s) (arity:=arity)) (v : Fin (r.val.shape r.property).vertices) :
    OrientedPerfectPairing ((r.val.shape r.property).arity v) := P (label r v)

def typedLinks (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
    (r : Input (s:=s) (arity:=arity)) := N.links (r.val.shape r.property) (pairing P r)

theorem port_eq_route (r : Input (s:=s) (arity:=arity)) (v : Fin r.val.vertices.length)
    (j : Fin (arity (label r v).val)) :
    N.port (r.val.shape r.property) v j = r.val.route r.property ⟨v,j⟩ := rfl

variable {K : Type*} [CommSemiring K]
variable (G : (i : Fin s) → Signature K (arity i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))

def nativeValue (r : Input (s:=s) (arity:=arity)) : K :=
  (r.val.realize r.property G (fun _ => Signature.disequality)).denote Fin.elim0

def signedQueryValue (r : Input (s:=s) (arity:=arity)) : K :=
  ∑y : Fin (r.val.edges.length*2) → Bool, ∏v : Fin r.val.vertices.length,
    GeneralEOPairedCSPCycles.compress (P (label r v)) (G (label r v))
      (N.signedInput (r.val.shape r.property) (pairing P r) y v)

theorem signedQuery_eq (r : Input (s:=s) (arity:=arity))
    (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) (hg : D.Good (typedLinks P r)) :
    signedQueryValue G P r =
      (2:K)^GeneralCSPUnused.unusedCount (D.scope (typedLinks P r)) * nativeValue G r :=
  N.signed_sum (r.val.realize r.property G (fun _ => Signature.disequality)) (pairing P r)
    (fun _ => rfl) (fun v => hf (label r v)) hg

theorem inconsistent_value (r : Input (s:=s) (arity:=arity))
    (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) (hg : ¬D.Good (typedLinks P r)) :
    nativeValue G r=0 :=
  N.inconsistent_denote (r.val.realize r.property G (fun _ => Signature.disequality)) (pairing P r)
    (fun _ => rfl) (fun v => hf (label r v)) hg

section Field
variable {F : Type*} [Field F] [CharZero F]
variable (H : (i : Fin s) → Signature F (arity i.val))
local instance (r : Input (s:=s) (arity:=arity)) : Decidable (D.Good (typedLinks P r)) :=
  Classical.propDecidable _

def normalizedValue (r : Input (s:=s) (arity:=arity)) : F :=
  if D.Good (typedLinks P r) then
    signedQueryValue H P r / (2:F)^GeneralCSPUnused.unusedCount (D.scope (typedLinks P r)) else 0

theorem normalized_eq (r : Input (s:=s) (arity:=arity))
    (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (H i)) :
    normalizedValue P H r = nativeValue H r := by
  classical
  by_cases hg : D.Good (typedLinks P r)
  · rw [normalizedValue,ite_eq_left hg,signedQuery_eq H P r hf hg]
    have hz : (2:F)^GeneralCSPUnused.unusedCount (D.scope (typedLinks P r)) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    field_simp
  · rw [normalizedValue,ite_eq_right hg,inconsistent_value H P r hf hg]
end Field
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeDecoded
