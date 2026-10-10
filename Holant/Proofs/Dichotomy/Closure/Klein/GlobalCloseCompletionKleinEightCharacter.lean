import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMOriginal
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterGauge

/-! Every stable real Pauli eight-port prime is character-flat, unless it
supplies an actual nonmatching q4. The signed-fiber phase is fully removed by
the checked invertible boundary programme, not assumed linear in advance. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightCharacter
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CharacterFlat
namespace H
export GlobalCloseCompletionKleinHigherNonaffine (Label Matching)
end H
namespace A
export GlobalCloseCompletionKleinEightRMOriginal (programme mapped_programme)
end A
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

theorem rm_character : CFlat (R.rm (K:=ℂ)) := by
  have same : R.rm (K:=ℂ)=rmCore := by
    funext x
    have words : (fun p=>boolEquiv (x p))=(fun p=>bit (x p)-(0 : BinaryVector 8) p) := by
      funext p
      change (if x p then 1 else 0)=(if x p then 1 else 0)-0
      rw [sub_zero]
    simp only [R.rm,rmCore,flatSignature,Units.val_one]
    rw [words]
  rw [same]
  exact Or.inr (flat_is_nonzeroFlat _ rmCore_flat)

theorem programme_iff (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool)
    (shifts : Fin 4→H.Label) (f : Signature ℂ 8) :
    CFlat (A.programme M phase shifts f) ↔ CFlat f := by
  rw [A.programme,GlobalCloseCompletionKleinCharacterGauge.phase_iff,
    GlobalCloseCompletionKleinCharacterGauge.translate_iff,GlobalCloseCompletionKleinCharacterGauge.reindex_iff]

theorem from_fiber (f : Signature ℂ 8) (M : H.Matching (Fin 8) 4)
    (phase : H.Label→Bool) (phase0 : phase 0=false) (shifts : Fin 4→H.Label) (shifts0 : shifts 0=0)
    (scale : ℂ) (normal : f=GlobalCloseCompletionKleinHigherNonaffine.Fiber.tensor M
      (fun a=>scale*(if phase a then -1 else 1)) (fun a e=>a+shifts e)) : CFlat f := by
  have mapped := A.mapped_programme (RingHom.id ℂ) M phase phase0 shifts shifts0 f scale normal
  have eq : A.programme M phase shifts f=(2*scale) • R.rm := mapped
  apply (programme_iff M phase shifts f).mp
  rw [eq]
  exact CFlat.smul _ rm_character _

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem stable_character (f : Signature (OI.K G) 8)
    (prime : Prime (⟨8,f⟩ : AnySignature (OI.K G))) (actual : Gadget.Realizes P.family .disequality f)
    (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    CFlat (RH.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f) ∨
    ∃q : Signature (OI.K G) 4,q≠0 ∧ Gadget.Realizes P.family .disequality q ∧
      ¬MatchingOrZero (actualTransfers P.family) q := by
  obtain ⟨c,hc,r,normal⟩ := GlobalCloseCompletionKleinStandardRealLine.current_realLine
    G P torsion cardinal noncyclic standard (n:=6) f (by decide) stable
  rcases GlobalCloseCompletionKleinHigherNonaffineEightNorm.normal_or_quaternary
    G P torsion cardinal noncyclic standard f prime actual stable r c hc normal with fiber|quaternary
  · obtain ⟨M,scale,phase,shifts,_nonzero,phase0,shifts0,normal⟩ := fiber
    exact Or.inl (from_fiber _ M phase phase0 shifts shifts0 scale normal)
  · exact Or.inr quaternary

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightCharacter
end
