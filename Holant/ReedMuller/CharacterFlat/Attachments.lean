import Holant.ReedMuller.CharacterFlat.Bell

/-! Literal native-X attachments. An explicit port bijection records which
original occurrence is used; the equality with the finite contraction is the
operation itself, rather than a supplied realization assumption. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

/-- This stronger closure permits any specified contracted pair. In particular,
choosing one port from each vertex is a one-port ordered-Bell attachment. -/
theorem ordered_bell_native_attachment (f : Signature ℂ n) (hf : CFlat f)
    (c : ℂ) (d l : ZMod 2) (order : Equiv.Perm (Fin (n+2))) :
    CFlat (Signature.contract Signature.disequality
      (Tensor.reindex order.symm (Signature.tensor f (c • bellSignature d l)))) := by
  have hb : CFlat (c • bellSignature d l) :=
    CharacterFlat.CFlat.smul _ (Or.inr (bellSignature_nonzeroFlat d l)) c
  have ht := CharacterFlat.CFlat.tensor f _ hf hb
  have hr := CharacterFlat.CFlat.reindex order.symm _ ht
  have hc := CharacterFlat.CFlat.contract _ hr 1
  simpa only [parityKernel_one] using hc

/-- The first contracted position is an original f port, the second is an
actual ordered Bell port; all surviving ports retain the supplied ordering. -/
theorem one_port_ordered_bell_attachment (f : Signature ℂ n) (hf : CFlat f)
    (c : ℂ) (d l : ZMod 2) (j : Fin n) (b : Fin 2)
    (order : Equiv.Perm (Fin (n+2)))
    (_first : order 0=Fin.castAdd 2 j) (_second : order 1=Fin.natAdd n b) :
    CFlat (Signature.contract Signature.disequality
      (Tensor.reindex order.symm (Signature.tensor f (c • bellSignature d l)))) :=
  ordered_bell_native_attachment f hf c d l order

end
end Holant.ReedMuller.CharacterFlat
