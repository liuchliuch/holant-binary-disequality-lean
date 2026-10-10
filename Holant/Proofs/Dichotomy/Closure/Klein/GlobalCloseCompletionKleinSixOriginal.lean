import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixRealClassification
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixCurrentCards
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixAnchorActual
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixAnchorUnique
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6RMOriginal
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterCurrentResources

/-! A genuine actual real six-port prime supplies a scalar H6 resource or an
actual nonmatching original-field quaternary. No assumption is made about
unexamined lower outputs; every finite probe is an actual original circuit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixOriginal
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
namespace A
export GlobalCloseCompletionKleinSixAnchorActual (gauge value map_gauge prime actual first_card)
end A
namespace C
export GlobalCloseCompletionKleinSixBellCoordinates (Normal)
end C
namespace B
export GlobalCloseCompletionKleinSixBellNorm (card)
end B
namespace D
export GlobalCloseCompletionKleinSixFiniteData (line)
end D
namespace S
export GlobalCloseCompletionKleinRMPhaseSource (index4)
end S
namespace H
export GlobalCloseCompletionKleinH6RMBell (core)
end H
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]

theorem gauge_real (phi : K→+*ℂ) (f : Signature K 6) (r : Signature ℝ 6)
    (c : ℂ) (normal : RH.mapSignature phi f=fun x=>c*(r x:ℂ)) (a : Fin 48) :
    RH.mapSignature phi (A.gauge a f)=fun x=>c*((A.gauge a r x:ℝ):ℂ) := by
  funext x
  rw [A.map_gauge,A.value,A.value]
  have h := congrFun normal (GlobalCloseCompletionKleinSixAnchorData.word a x)
  change phi (f _)=c*(r _:ℂ) at h
  change (GlobalCloseCompletionKleinSixAnchorData.weight a x:ℂ)*phi (f _)=_
  rw [h,Complex.ofReal_mul,Complex.ofReal_intCast]
  ring

theorem reindex_real (phi : K→+*ℂ) (f : Signature K 6) (r : Signature ℝ 6)
    (c : ℂ) (normal : RH.mapSignature phi f=fun x=>c*(r x:ℂ)) (p : Equiv.Perm (Fin 6)) :
    RH.mapSignature phi (Tensor.reindex p f)=fun x=>c*((Tensor.reindex p r x:ℝ):ℂ) := by
  funext x
  exact congrFun normal (fun i=>x (p i))

theorem h6_mapped (phi : K→+*ℂ) (f : Signature K 6) (r : Signature ℝ 6)
    (c : ℂ) (normal : RH.mapSignature phi f=fun x=>c*(r x:ℂ))
    (p : Equiv.Perm (Fin 6)) (d : ℝ) (form : r=d • Tensor.reindex p H.core) :
    RH.mapSignature phi (Tensor.reindex p.symm f)=(c*(d:ℂ)) • H.core := by
  funext x
  have h := congrFun normal (fun i=>x (p.symm i))
  change phi (f (fun i=>x (p.symm i)))=c*(r (fun i=>x (p.symm i)):ℂ) at h
  change phi (f (fun i=>x (p.symm i)))=(c*(d:ℂ))*H.core x
  rw [h,form]
  simp only [Pi.smul_apply,smul_eq_mul,Tensor.reindex,Equiv.symm_apply_apply,
    Complex.ofReal_mul,←GlobalCloseCompletionKleinH6RMOriginal.map_core_apply Complex.ofRealHom]
  change c*((d:ℂ)*(H.core (K:=ℝ) x:ℂ))=(c*(d:ℂ))*(H.core (K:=ℝ) x:ℂ)
  ring

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem source (f : Signature (OI.K G) 6)
    (prime : Prime (⟨6,f⟩ : AnySignature (OI.K G))) (actual : Gadget.RealizesUpTo P.family .disequality f)
    (r : Signature ℝ 6) (c : ℂ) (hc : c≠0)
    (normal : RH.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=fun x=>c*(r x:ℂ)) :
    (∃d : OI.K G,d≠0 ∧ Gadget.Realizes P.family .disequality (d • H.core)) ∨
    ∃q : Signature (OI.K G) 4,q≠0 ∧ Gadget.Realizes P.family .disequality q ∧
      ¬MatchingOrZero (actualTransfers P.family) q := by
  classical
  by_cases exit : ∃q : Signature (OI.K G) 4,q≠0 ∧ Gadget.Realizes P.family .disequality q ∧
      ¬MatchingOrZero (actualTransfers P.family) q
  · exact Or.inr exit
  have base := GlobalCloseCompletionKleinSixCurrentCards.from_upTo
    G P torsion cardinal noncyclic standard f prime actual r c hc normal
  obtain ⟨R⟩ := base.resolve_right exit
  let af := A.gauge (R.label 0) f
  let ar := A.gauge (R.label 0) r
  have ag := A.prime (R.label 0) f prime
  have normalA := gauge_real (ClosurePhysicalBridge.complexEmbedding G) f r c normal (R.label 0)
  have J := GlobalCloseCompletionKleinCharacterCurrentResources.bell_actual G P torsion cardinal noncyclic standard 1 1
  have actualA := A.actual P.family P.equality J (R.label 0) f actual
  have allOrders (p : Equiv.Perm (Fin 6)) : Nonempty (C.Normal (Tensor.reindex p ar)) := by
    have actualP := Holant.OpenNetworkComposition.ProjectiveSubstitution.realizesUpTo_reindex
      P.family p af actualA
    have primeP := GlobalCloseCompletionKleinGramAllPairs.prime_reindex af ag p
    have normalP := reindex_real (ClosurePhysicalBridge.complexEmbedding G) af ar c normalA p
    exact (GlobalCloseCompletionKleinSixCurrentCards.from_upTo
      G P torsion cardinal noncyclic standard _ primeP actualP _ c hc normalP).resolve_right exit
  have current : Nonempty (C.Normal ar) := by simpa only [Tensor.reindex_refl] using allOrders (Equiv.refl _)
  obtain ⟨T⟩ := current
  have first (z : Fin 4→Bool) : B.card r 0 z=R.scale*(D.line (R.label 0) (S.index4 z):ℝ) := by
    have h := R.value 0 (S.index4 z)
    rw [GlobalCloseCompletionKleinRMPhaseSupport.word_index] at h
    simpa only [R.phase_zero,GlobalCloseCompletionKleinSixMatchingCoordinates.sign,
      Bool.false_eq_true,ite_false,Int.cast_one,mul_one] using h
  have anchored := GlobalCloseCompletionKleinSixAnchorUnique.label_zero ar T R.scale R.scale_nonzero
    (A.first_card (R.label 0) r R.scale first)
  rcases GlobalCloseCompletionKleinSixRealClassification.classify ar T anchored.1
    (fun j=>allOrders (GlobalCloseCompletionKleinSixCrossCoordinates.order j)) with split|core
  · obtain ⟨u,v,⟨split⟩⟩ := split
    exact (ag.2 (GlobalCloseCompletionKleinGramTransport.real_split_descends
      (ClosurePhysicalBridge.complexEmbedding G) af ag.1 ar c hc normalA split)).elim
  · obtain ⟨p,d,hd,form⟩ := core
    have mapped := h6_mapped (ClosurePhysicalBridge.complexEmbedding G) af ar c normalA p d form
    have nonzero : c*(d:ℂ)≠0 := mul_ne_zero hc (by exact_mod_cast hd)
    obtain ⟨v,hv,equation⟩ := GlobalCloseCompletionKleinH6RMOriginal.recover_scale
      (ClosurePhysicalBridge.complexEmbedding G) (Tensor.reindex p.symm af) _ nonzero mapped
    have actualP := Holant.OpenNetworkComposition.ProjectiveSubstitution.realizesUpTo_reindex
      P.family p.symm af actualA
    obtain ⟨u,hu,realizes⟩ := actualP
    rw [equation] at realizes
    left
    refine ⟨u*v,mul_ne_zero hu hv,?_⟩
    convert realizes using 1
    funext x
    change (u*v)*H.core x=u*(v*H.core x)
    ring

include cardinal noncyclic standard in
theorem rm_source (f : Signature (OI.K G) 6)
    (prime : Prime (⟨6,f⟩ : AnySignature (OI.K G))) (actual : Gadget.RealizesUpTo P.family .disequality f)
    (r : Signature ℝ 6) (c : ℂ) (hc : c≠0)
    (normal : RH.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=fun x=>c*(r x:ℂ)) :
    (∃d : OI.K G,d≠0 ∧ Gadget.Realizes P.family .disequality (d • GlobalCloseCompletionC2RMActual.rm)) ∨
    ∃q : Signature (OI.K G) 4,q≠0 ∧ Gadget.Realizes P.family .disequality q ∧
      ¬MatchingOrZero (actualTransfers P.family) q := by
  rcases source G P torsion cardinal noncyclic standard f prime actual r c hc normal with core|quaternary
  · obtain ⟨d,hd,actualH⟩ := core
    exact Or.inl (GlobalCloseCompletionKleinH6RMActual.rm_actual P.family P.equality d hd actualH)
  · exact Or.inr quaternary


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixOriginal
end
