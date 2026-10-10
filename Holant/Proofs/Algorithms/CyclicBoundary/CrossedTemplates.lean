import Holant.Proofs.Algorithms.CyclicBoundary.ZeroEndpointRealization
import Holant.OpenNetworkComposition.ProjectiveSubstitutionPorts


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.CrossedTemplates
open Holant.Certificates.FourthRootOdd Holant.Certificates.TwelveLoops
open Holant.ReedMuller.CoefficientAtlas
open TwoCopyKernels TwoCopyTransport ZeroEndpointDressing PhysicalAttachments
noncomputable section

def swapPorts (p : Fin 6) : Equiv.Perm (Fin 4) :=
  Equiv.swap (portEquiv p 0) (portEquiv p 1)

def swapped (q : Signature ℂ 4) (p : Fin 6) : Signature ℂ 4 := Tensor.reindex (swapPorts p) q

theorem swapped_word (q : Signature ℂ 4) (p : Fin 6) (u v : Bool) (x : Fin 2 → Bool) :
    swapped q p (insertPair p u v x) = q (insertPair p v u x) := by
  unfold swapped Tensor.reindex
  congr 1
  funext i
  fin_cases p <;> fin_cases i <;>
    simp [swapPorts,insertPair,portEquiv,portOrder,portInverse,Equiv.swap_apply_def]

theorem swapped_physical (q : Signature ℂ 4) (p : Fin 6) :
    swapped (physical q) p = physical (swapped q p) := by
  unfold swapped physical
  rw [coordinateAction_reindex]

def analyticStraight (q : Signature ℂ 4) (p : Fin 6) : Signature ℂ 4 :=
  contraction q q p (TwoCopyKernels.diagonal 1 (-1)) (TwoCopyKernels.diagonal 1 (-1))

def analyticCrossed (q : Signature ℂ 4) (p : Fin 6) : Signature ℂ 4 :=
  contraction q (swapped q p) p (TwoCopyKernels.diagonal 1 (-1)) (TwoCopyKernels.diagonal 1 (-1))

def nativeCrossed (q : Signature ℂ 4) (p : Fin 6) : Signature ℂ 4 :=
  contraction q (swapped q p) p Signature.disequality Signature.disequality

theorem native_four (f g : Signature ℂ 4) (p : Fin 6) :
    contraction (physical f) (physical g) p Signature.disequality Signature.disequality =
      (4:ℂ) • physical (contraction f g p
        (TwoCopyKernels.diagonal 1 (-1)) (TwoCopyKernels.diagonal 1 (-1))) := by
  unfold physical
  rw [contraction_action,ZeroEndpointRealization.native_hadamard_edge]
  have h := contraction_scales 1 1 2 2 f g p
    (TwoCopyKernels.diagonal 1 (-1)) (TwoCopyKernels.diagonal 1 (-1))
  simp only [one_smul] at h
  norm_num at h
  rw [h,action_scale]

theorem native_crossed_formula (q : Signature ℂ 4) (p : Fin 6) :
    nativeCrossed (physical q) p = (4:ℂ) • physical (analyticCrossed q p) := by
  rw [nativeCrossed,swapped_physical,native_four]
  rfl

theorem actual_crossed {F : SignatureFamily ℂ} (q : Signature ℂ 4)
    (hq : Gadget.RealizesUpTo F .disequality (physical q)) (p : Fin 6) :
    Gadget.RealizesUpTo F .disequality (physical (analyticCrossed q p)) := by
  have hs := OpenNetworkComposition.ProjectiveSubstitution.realizesUpTo_reindex F
    (swapPorts p) (physical q) hq
  have h := native_realizesUpTo F (physical q) (swapped (physical q) p)
    hq hs p (by norm_num)
  change Gadget.RealizesUpTo F .disequality (nativeCrossed (physical q) p) at h
  rw [native_crossed_formula] at h
  exact upTo_of_scale _ 4 (by norm_num) h

theorem actual_straight {F : SignatureFamily ℂ} (q : Signature ℂ 4)
    (hq : Gadget.RealizesUpTo F .disequality (physical q)) (p : Fin 6) :
    Gadget.RealizesUpTo F .disequality (physical (analyticStraight q p)) := by
  have h := native_realizesUpTo F (physical q) (physical q) hq hq p (by norm_num)
  rw [native_four] at h
  exact upTo_of_scale _ 4 (by norm_num) h

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.CrossedTemplates
