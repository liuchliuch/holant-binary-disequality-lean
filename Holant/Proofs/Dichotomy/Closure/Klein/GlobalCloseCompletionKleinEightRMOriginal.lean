import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMGauge
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterCurrentResources
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinRMPhaseProgram

/-! A stable original-field Pauli eight-port prime supplies genuine scalar
RM8, or an actual nonmatching quaternary. The full signed fiber, port chart,
linear signs and every original-field substitution multiplier are consumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMOriginal
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
namespace H
export GlobalCloseCompletionKleinHigherNonaffine (Label Matching)
end H
namespace F
export GlobalCloseCompletionKleinEightRMFiber (basisOrder realFiber complex_fiber)
end F
namespace C
export GlobalCloseCompletionKleinEightRMLabels (phasePack shiftPack)
end C
namespace D
export GlobalCloseCompletionKleinEightRMData (order mask)
end D
namespace A
export GlobalCloseCompletionKleinPhaseActual (phase phase_actual translate_upTo)
end A
namespace T
export GlobalCloseCompletionC2BitTranslateActual (translate)
end T
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace Q
export GlobalCloseCompletionKleinEightRMGauge (phaseSet normalized)
end Q
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K V : Type*} [Field K] [Field V]

def programme (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool) (shifts : Fin 4→H.Label)
    (f : Signature K 8) : Signature K 8 :=
  A.phase (Q.phaseSet phase shifts)
    (T.translate (Tensor.reindex ((F.basisOrder M).trans (D.order (C.phasePack phase))) f)
      (D.mask (C.phasePack phase) (C.shiftPack shifts)))

theorem programme_scale (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool) (shifts : Fin 4→H.Label)
    (f : Signature K 8) (c : K) : programme M phase shifts (c • f)=c • programme M phase shifts f := by
  rw [programme,GlobalCloseCompletionKleinRMPhaseProgram.reindex_scale,
    GlobalCloseCompletionKleinRMPhaseProgram.translate_scale,GlobalCloseCompletionKleinRMPhaseProgram.phase_scale]
  rfl

theorem map_programme (phi : K→+*V) (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool)
    (shifts : Fin 4→H.Label) (f : Signature K 8) :
    RH.mapSignature phi (programme M phase shifts f)=programme M phase shifts (RH.mapSignature phi f) := by
  funext x
  simp only [programme,A.phase,T.translate,Tensor.reindex,RH.mapSignature,map_mul,map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp

theorem map_rm (phi : K→+*V) : RH.mapSignature phi (R.rm (K:=K))=R.rm := by
  funext x
  simp only [RH.mapSignature,R.rm]
  split_ifs <;> simp

theorem rm_zero : R.rm (K:=K) (fun _=>false)=1 := by
  rw [GlobalCloseCompletionKleinH6RMBell.rm_check]
  norm_num [GlobalCloseCompletionKleinH6RMBell.rmCheck]

theorem recover_rm (phi : K→+*V) (f : Signature K 8) (c : V) (hc : c≠0)
    (normal : RH.mapSignature phi f=c • R.rm) : ∃d : K,d≠0 ∧ f=d • R.rm := by
  have zero := congrFun normal (fun _=>false)
  change phi (f (fun _=>false))=c*R.rm (fun _=>false) at zero
  rw [rm_zero,mul_one] at zero
  refine ⟨f (fun _=>false),?_,?_⟩
  · intro h
    exact hc (zero.symm.trans (by rw [h,map_zero]))
  · funext x
    apply phi.injective
    change phi (f x)=phi (f (fun _=>false)*R.rm x)
    rw [map_mul,zero]
    have h := congrFun (map_rm phi) x
    change phi (R.rm x)=R.rm x at h
    rw [h]
    exact congrFun normal x

theorem actual_programme (family : SignatureFamily K) (identity : RetainsIdentity family)
    (J : Gadget.RealizesUpTo family .disequality (GlobalCloseCompletionKleinCharacterResources.bell 1 1))
    (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool) (shifts : Fin 4→H.Label)
    (f : Signature K 8) (actual : Gadget.RealizesUpTo family .disequality f) :
    Gadget.RealizesUpTo family .disequality (programme M phase shifts f) := by
  have reordered := Holant.OpenNetworkComposition.ProjectiveSubstitution.realizesUpTo_reindex
    family ((F.basisOrder M).trans (D.order (C.phasePack phase))) f actual
  have shifted := A.translate_upTo family identity _ reordered (D.mask (C.phasePack phase) (C.shiftPack shifts))
  exact A.phase_actual family J _ shifted (Q.phaseSet phase shifts)

theorem mapped_programme (phi : K→+*ℂ) (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool)
    (phase0 : phase 0=false) (shifts : Fin 4→H.Label) (shifts0 : shifts 0=0)
    (f : Signature K 8) (scale : ℂ)
    (normal : RH.mapSignature phi f=GlobalCloseCompletionKleinHigherNonaffine.Fiber.tensor M
      (fun a=>scale*(if phase a then -1 else 1)) (fun a e=>a+shifts e)) :
    RH.mapSignature phi (programme M phase shifts f)=(2*scale) • R.rm := by
  rw [map_programme,normal,F.complex_fiber]
  change programme M phase shifts (scale • RH.mapSignature Complex.ofRealHom (F.realFiber M phase shifts))=_
  rw [programme_scale,←map_programme]
  have value : programme M phase shifts (F.realFiber M phase shifts)=(2:ℝ) • R.rm :=
    Q.normalized M phase phase0 shifts shifts0
  rw [value]
  funext x
  change scale*Complex.ofRealHom (2*R.rm x)=(2*scale)*R.rm x
  rw [map_mul,map_ofNat]
  have h := congrFun (map_rm Complex.ofRealHom) x
  change Complex.ofRealHom (R.rm x)=R.rm x at h
  rw [h]
  ring

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem from_fiber (f : Signature (OI.K G) 8) (actual : Gadget.Realizes P.family .disequality f)
    (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool) (phase0 : phase 0=false)
    (shifts : Fin 4→H.Label) (shifts0 : shifts 0=0) (scale : ℂ) (nonzero : scale≠0)
    (normal : RH.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=
      GlobalCloseCompletionKleinHigherNonaffine.Fiber.tensor M
        (fun a=>scale*(if phase a then -1 else 1)) (fun a e=>a+shifts e)) :
    ∃d : OI.K G,d≠0 ∧ Gadget.Realizes P.family .disequality (d • R.rm) := by
  have J := GlobalCloseCompletionKleinCharacterCurrentResources.bell_actual G P torsion cardinal noncyclic standard 1 1
  have actual' := actual_programme P.family P.equality J M phase shifts f ⟨1,one_ne_zero,by simpa using actual⟩
  have mapped := mapped_programme (ClosurePhysicalBridge.complexEmbedding G) M phase phase0 shifts shifts0 f scale normal
  obtain ⟨d,hd,equation⟩ := recover_rm (ClosurePhysicalBridge.complexEmbedding G) _ (2*scale)
    (mul_ne_zero (by norm_num) nonzero) mapped
  obtain ⟨u,hu,realizes⟩ := actual'
  rw [equation] at realizes
  refine ⟨u*d,mul_ne_zero hu hd,?_⟩
  convert realizes using 1
  funext x
  change (u*d)*R.rm x=u*(d*R.rm x)
  ring

include cardinal noncyclic standard in
theorem stable_source (f : Signature (OI.K G) 8)
    (prime : Prime (⟨8,f⟩ : AnySignature (OI.K G))) (actual : Gadget.Realizes P.family .disequality f)
    (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    (∃d : OI.K G,d≠0 ∧ Gadget.Realizes P.family .disequality (d • R.rm)) ∨
      ∃q : Signature (OI.K G) 4,q≠0 ∧ Gadget.Realizes P.family .disequality q ∧
        ¬MatchingOrZero (actualTransfers P.family) q := by
  obtain ⟨c,hc,r,normal⟩ := GlobalCloseCompletionKleinStandardRealLine.current_realLine
    G P torsion cardinal noncyclic standard (n:=6) f (by decide) stable
  rcases GlobalCloseCompletionKleinHigherNonaffineEightNorm.normal_or_quaternary
    G P torsion cardinal noncyclic standard f prime actual stable r c hc normal with fiber|quaternary
  · obtain ⟨M,scale,phase,shifts,nonzero,phase0,shifts0,normal⟩ := fiber
    exact Or.inl (from_fiber G P torsion cardinal noncyclic standard f actual M phase phase0 shifts shifts0 scale nonzero normal)
  · exact Or.inr quaternary


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMOriginal
end
