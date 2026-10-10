import Holant.Certificates.EqualityQuaternary.Source


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.C2Bridge
open Holant.Marked Holant.Tractable
open Holant.Projective.CyclicQuaternary Holant.Projective.CyclicPhasePencil
open Holant.Projective.CyclicQuaternary.Physical hiding Scalar Mat
open Holant.Certificates.EqualityQuaternary
noncomputable section

def literalRepresentatives (F : SignatureFamily Scalar)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar) ∈ F) :
    C2.Representatives F where
  matrix := C2.binary
  multiplier := fun _ => 1
  multiplier_ne_zero := fun _ => one_ne_zero
  actual := by
    intro p
    cases p
    · exact Gadget.realizes_of_mem F .disequality _ hI
    · exact Gadget.realizes_edgeBox (K := Scalar) F .disequality
  normal_form := by intro p; funext u v; simp [scale]

def root (p : Bool) : Scalar := if p then 1 else -1

theorem root_square (p : Bool) : (root p)^2=1 := by cases p <;> norm_num [root]

theorem literal_walsh_form (p : Bool) :
    walshBinary (C2.binary p) = (1/2:Scalar) • Kernel.mul (phase (root p)) Holant.Projective.CyclicPhasePencil.Z := by
  funext u v
  cases p <;> cases u <;> cases v <;>
    norm_num [walshBinary,Pinv,P,C2.binary,root,Kernel.mul,Kernel.transpose,
      phase,Holant.Projective.CyclicPhasePencil.Z,diagonal,Signature.equality,Signature.disequality]

def reconstruct (T : Mat) : Mat :=
  Kernel.mul (Kernel.mul P (Kernel.mul T Holant.Projective.CyclicPhasePencil.Z)) (Kernel.transpose P)

theorem reconstruct_transfer (B : Mat) : reconstruct (Kernel.mul (walshBinary B) Holant.Projective.CyclicPhasePencil.Z)=B := by
  funext u v
  cases u <;> cases v <;>
    simp [reconstruct,walshBinary,Pinv,P,Kernel.mul,Kernel.transpose,Holant.Projective.CyclicPhasePencil.Z,diagonal] <;> ring

theorem reconstruct_phase (p : Bool) (c : Scalar) :
    reconstruct (c • phase (root p)) = scale (2*c) (C2.binary p) := by
  funext u v
  cases p <;> cases u <;> cases v <;>
    simp [reconstruct,root,C2.binary,scale,phase,Holant.Projective.CyclicPhasePencil.Z,diagonal,P,Kernel.mul,
      Kernel.transpose,Signature.equality,Signature.disequality] <;> ring

theorem root_cases (s : Scalar) (hs : s^2=1) : s=1 ∨ s=-1 := by
  have hh : (s-1)*(s+1)=0 := by linear_combination hs
  rcases mul_eq_zero.mp hh with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- A cyclic transfer of order dividing two is precisely one of the two
physical lines after undoing the analytic Walsh action. The scale 2 is kept. -/
theorem transfer_to_line (F : SignatureFamily Scalar)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar) ∈ F)
    (B : Mat) (h : Kernel.mul (walshBinary B) Holant.Projective.CyclicPhasePencil.Z=0 ∨
      IsPhase 2 (Kernel.mul (walshBinary B) Holant.Projective.CyclicPhasePencil.Z)) :
    B=0 ∨ C2.ActualLine (literalRepresentatives F hI) B := by
  rcases h with hz | ⟨s,c,hs,hc,he⟩
  · left
    have hh := congrArg reconstruct hz
    rw [reconstruct_transfer] at hh
    refine hh.trans ?_
    funext a b
    cases a <;> cases b <;> norm_num [reconstruct, Kernel.mul, P,
      Holant.Projective.CyclicPhasePencil.Z, diagonal, Kernel.transpose]
  · right
    obtain ⟨p,hp⟩ : ∃ p : Bool, s=root p := by
      rcases root_cases s hs with h | h
      · exact ⟨true,h⟩
      · exact ⟨false,h⟩
    have hh := congrArg reconstruct he
    rw [reconstruct_transfer,hp,reconstruct_phase] at hh
    exact ⟨p,2*c,mul_ne_zero (by norm_num) hc,hh⟩

theorem physical_deck (F : SignatureFamily Scalar)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar) ∈ F)
    (q : Signature Scalar 4) (hd : AllPhaseCards 2 (walsh q)) :
    C2.PhysicalDeck (literalRepresentatives F hI) q := by
  intro i side order p
  apply transfer_to_line F hI
  change physicalTransfer q i side order (C2.binary p)=0 ∨
    IsPhase 2 (physicalTransfer q i side order (C2.binary p))
  rw [physicalTransfer_phase q i side order _ (root p) (1/2) (literal_walsh_form p)]
  exact (zero_or_phase_smul_iff 2 _ (by norm_num) _).mpr
    (hd i side order (root p) (root_square p))

/-- This is the exact counted-network conclusion available in the N=2
row. In the exceptional mixed-sign case, nonmatching must still be consumed
by actual factor retention/binary dispatch; it is not strengthened for free. -/
theorem source_order_two (F : SignatureFamily Scalar) (q : Signature Scalar 4)
    (hq : (⟨4,q⟩ : AnySignature Scalar) ∈ F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar) ∈ F)
    (hp : TensorPrime q) (hd : AllPhaseCards 2 (walsh q)) :
    ∃ N : Network Scalar 4, Counted.Allowed q N ∧ Counted.copies N≤2 ∧
      Holant.EightVertex.ProductAnchor.EndpointEven N.denote ∧
      ¬GroupMatching C2.group N.denote ∧ Gadget.Realizes F .disequality N.denote :=
  C2.source_C2_boundary F (literalRepresentatives F hI) q hp hq hI (physical_deck F hI q hd)

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.C2Bridge
