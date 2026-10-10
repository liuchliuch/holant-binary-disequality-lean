import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedEqualityMask

/-! One actual original-field rotation turns the selected shifted equality
mask into a nonzero scalar even-parity q4 in the original coordinates. The
basis only verifies its value; its square root is never a source label. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedParity
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Marked.SupportAtlas Holant.Certificates.EqualityQuaternary
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.OpenNetworkComposition
namespace M
export GlobalCloseCompletionShiftedMask
  (basis selected phi originalMask originalMask_actual map_splice masked_prime)
end M
namespace E
export GlobalCloseCompletionShiftedEqualityMask (Choice choose)
end E
namespace CQ
export Holant.Projective.CyclicQuaternary (ofCoordinates)
end CQ
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (native : GlobalCloseCompletionShiftedMarking.Native G P torsion)

abbrev phaseIndex (t : Phase (M.selected G P torsion native).m) :=
  HistorySectorNormalized.phaseIndex G P torsion (M.basis G P torsion native)
    (M.selected G P torsion native) false t
abbrev binary (t : Phase (M.selected G P torsion native).m) :=
  actualRepresentative P.family torsion (phaseIndex G P torsion native t).key
abbrev coefficient (t : Phase (M.selected G P torsion native).m) :=
  (phaseIndex G P torsion native t).multiplier

def rotationPhase (a h : Scalar) (hr : Roots (M.selected G P torsion native).m (h/a)) :
    Phase (M.selected G P torsion native).m :=
  ⟨native.reflection.eta^2/(h/a),by
    apply Roots.div _ hr
    change (native.reflection.eta^2)^(M.selected G P torsion native).m=1
    rw [←pow_mul]
    exact native.reflection.eta_root native.axis native.notTwo native.notFour⟩

variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

def value (mask : Word) (t : Phase (M.selected G P torsion native).m) : Signature (OI.K G) 4 :=
  spliceTensor (M.originalMask G P torsion native q mask)
    (Holant.Projective.BoundedTorsion.binarySignature (binary G P torsion native t)) 0

include core literal in
theorem value_actual (mask : Word) (t : Phase (M.selected G P torsion native).m) :
    Gadget.Realizes P.family .disequality (value G P torsion native q mask t) :=
  realizes_splice P.family _ _ (M.originalMask_actual G P torsion native q core literal mask)
    (actualRepresentative_actual P.family torsion (phaseIndex G P torsion native t).key).1 0

theorem rotation_sector (mask : Word) (t : Phase (M.selected G P torsion native).m) (a h : Scalar)
    (he : (M.basis G P torsion native).symm.action
      (RingHomRealization.mapSignature (M.phi G) (M.originalMask G P torsion native q mask))=
        CQ.ofCoordinates a h (fun _=>(0,0))) :
    (M.basis G P torsion native).symm.action
      (RingHomRealization.mapSignature (M.phi G) (value G P torsion native q mask t))=
      CQ.ofCoordinates (coefficient G P torsion native t*a)
        (coefficient G P torsion native t*t.val*h) (fun _=>(0,0)) := by
  have ht := (phaseIndex G P torsion native t).transfer
  change sectorTransfer (M.basis G P torsion native)
    ((binary G P torsion native t).map (M.phi G))=
      scale (coefficient G P torsion native t) (R t.val) at ht
  unfold value
  rw [M.map_splice,←Holant.Projective.CyclicDressing.onePort_eq_splice,
    sector_onePort_action,ht,he]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Signature.coordinateAction,Holant.Projective.CyclicQuaternary.Physical.sum_words4,
      Fin.prod_univ_succ,CQ.ofCoordinates,R,diagonalKernel,scale,Signature.equality,h0,h1,h2,h3] <;> ring

def evenTable {K : Type*} [Zero K] [One K] : Signature K 4 :=
  fun x=>if Holant.weight x % 2=0 then 1 else 0

theorem return_even (a : Scalar) : (M.basis G P torsion native).action
    (CQ.ofCoordinates a (a*native.reflection.eta^2) (fun _=>(0,0)))=(2*a) • evenTable := by
  have hu : (Finset.univ : Finset (Fin 4))={0,1,2,3} := by decide
  have hb : native.reflection.square^4*native.reflection.eta^2=1 := by
    calc
      _=(native.reflection.square^2*native.reflection.eta)^2 := by ring
      _=1 := by rw [native.reflection.square_eq]; simp [native.reflection.eta_nonzero]
  change (basisA native.reflection.square native.reflection.square_nonzero).action _=_
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [basisA,UA,InvertibleKernel.action,Signature.coordinateAction,
      Holant.Projective.CyclicQuaternary.Physical.sum_words4,Fin.prod_univ_succ,
      CQ.ofCoordinates,evenTable,Holant.weight,hu,Finset.filter_insert,Finset.filter_singleton,
      h0,h1,h2,h3,smul_eq_mul]
  all_goals first | linear_combination a*hb | linear_combination -a*hb |
    linear_combination 2*a*hb | linear_combination -2*a*hb

theorem physical_value (mask : Word) (a h : Scalar) (ha : a≠0) (hh : h≠0)
    (hr : Roots (M.selected G P torsion native).m (h/a))
    (he : (M.basis G P torsion native).symm.action
      (RingHomRealization.mapSignature (M.phi G) (M.originalMask G P torsion native q mask))=
        CQ.ofCoordinates a h (fun _=>(0,0))) :
    RingHomRealization.mapSignature (M.phi G)
      (value G P torsion native q mask (rotationPhase G P torsion native a h hr))=
      (2*(coefficient G P torsion native (rotationPhase G P torsion native a h hr)*a)) • evenTable := by
  let t := rotationPhase G P torsion native a h hr
  have hth : t.val*h=a*native.reflection.eta^2 := by
    dsimp [t,rotationPhase]
    field_simp [ha,hh] <;> ring
  have hv := rotation_sector G P torsion native q mask t a h he
  have hc : coefficient G P torsion native t*t.val*h=
      (coefficient G P torsion native t*a)*native.reflection.eta^2 := by
    rw [mul_assoc,hth]
    ring
  rw [hc] at hv
  have back := congrArg (M.basis G P torsion native).action hv
  rw [InvertibleKernel.action_symm_action,return_even] at back
  exact back

include core literal in
theorem value_prime (mask : Word) (t : Phase (M.selected G P torsion native).m) :
    Prime (⟨4,value G P torsion native q mask t⟩ : AnySignature (OI.K G)) := by
  let c := coefficient G P torsion native t
  have hc : c≠0 := (phaseIndex G P torsion native t).nonzero
  have ht := t.property.ne_zero (by have := (M.selected G P torsion native).range; omega)
  let A : Fin 4→Mat := fun i=>if i=0 then scale c (R t.val) else Signature.equality
  let B : Fin 4→Mat := fun i=>if i=0 then diagonalKernel c⁻¹ (c*t.val)⁻¹ else Signature.equality
  have hinv : ∀i,Kernel.mul (B i) (A i)=Signature.equality := by
    intro i
    by_cases hi : i=0
    · funext u v
      cases u <;> cases v <;>
        simp [A,B,hi,R,scale,diagonalKernel,Kernel.mul_apply,Signature.equality,hc,ht] <;> field_simp [hc,ht]
    · simp [A,B,hi,Kernel.equality_mul]
  have hp := prime_coordinateAction (M.masked_prime G P torsion native q core literal mask) A B hinv
  have sector := (phaseIndex G P torsion native t).transfer
  change sectorTransfer (M.basis G P torsion native) ((binary G P torsion native t).map (M.phi G))=
    scale c (R t.val) at sector
  have he : (M.basis G P torsion native).symm.action
      (RingHomRealization.mapSignature (M.phi G) (value G P torsion native q mask t))=
      Signature.coordinateAction A ((M.basis G P torsion native).symm.action
        (RingHomRealization.mapSignature (M.phi G) (M.originalMask G P torsion native q mask))) := by
    unfold value
    rw [M.map_splice,←Holant.Projective.CyclicDressing.onePort_eq_splice,sector_onePort_action,sector]
  rw [←he] at hp
  have back := prime_coordinateAction hp (fun _=>(M.basis G P torsion native).matrix)
    (fun _=>(M.basis G P torsion native).inverse) (fun _=>(M.basis G P torsion native).inverse_matrix)
  have physical : TensorPrime (RingHomRealization.mapSignature (M.phi G)
      (value G P torsion native q mask t)) := by
    change TensorPrime ((M.basis G P torsion native).action
      ((M.basis G P torsion native).symm.action _)) at back
    simpa only [InvertibleKernel.action_symm_action] using back
  apply (prime_mapSignature_iff (M.phi G) _).mp
  exact (PrimalityInterfaces.retained_equality_prime _).mpr physical

abbrev choice := E.choose G P torsion native q core literal stable
abbrev phase := rotationPhase G P torsion native (choice G P torsion native q core literal stable).left
  (choice G P torsion native q core literal stable).right (choice G P torsion native q core literal stable).ratio
abbrev output := value G P torsion native q (choice G P torsion native q core literal stable).mask
  (phase G P torsion native q core literal stable)
abbrev complexScalar := 2*(coefficient G P torsion native (phase G P torsion native q core literal stable)*
  (choice G P torsion native q core literal stable).left)
def scalar : OI.K G := output G P torsion native q core literal stable (fun _=>false)

theorem ambient_value : RingHomRealization.mapSignature (M.phi G)
    (output G P torsion native q core literal stable)=
      (complexScalar G P torsion native q core literal stable) • evenTable :=
  physical_value G P torsion native q (choice G P torsion native q core literal stable).mask _ _
    (choice G P torsion native q core literal stable).left_nonzero
    (choice G P torsion native q core literal stable).right_nonzero
    (choice G P torsion native q core literal stable).ratio
    (choice G P torsion native q core literal stable).exact

theorem scalar_value : M.phi G (scalar G P torsion native q core literal stable)=
    complexScalar G P torsion native q core literal stable := by
  have h := congrFun (ambient_value G P torsion native q core literal stable) (fun _=>false)
  simpa [scalar,RingHomRealization.mapSignature,evenTable,Holant.weight] using h

theorem scalar_nonzero : scalar G P torsion native q core literal stable≠0 := by
  have hc : complexScalar G P torsion native q core literal stable≠0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (phaseIndex G P torsion native _).nonzero
      (choice G P torsion native q core literal stable).left_nonzero)
  intro zero
  apply hc
  rw [←scalar_value,zero,map_zero]

theorem output_eq : output G P torsion native q core literal stable=
    scalar G P torsion native q core literal stable • evenTable := by
  funext x
  apply (M.phi G).injective
  have h := congrFun (ambient_value G P torsion native q core literal stable) x
  change M.phi G (output G P torsion native q core literal stable x)=
    M.phi G ((scalar G P torsion native q core literal stable)*evenTable x)
  rw [map_mul,scalar_value]
  change M.phi G (output G P torsion native q core literal stable x)=
    complexScalar G P torsion native q core literal stable *
      M.phi G (if Holant.weight x % 2=0 then 1 else 0)
  have mapped : M.phi G (if Holant.weight x % 2=0 then (1 : OI.K G) else 0)=
      (if Holant.weight x % 2=0 then (1 : Scalar) else 0) := by
    split <;> simp
  rw [mapped]
  exact h

def direct : DeckDirect P.family (output G P torsion native q core literal stable) :=
  DeckDirect.ofRealizes P.equality (value_actual G P torsion native q core literal _ _)

def access := currentSignatureAccess G P
  ⟨4,output G P torsion native q core literal stable⟩ (value_actual G P torsion native q core literal _ _)

theorem output_prime : Prime (⟨4,output G P torsion native q core literal stable⟩ : AnySignature (OI.K G)) :=
  value_prime G P torsion native q core literal _ _


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedParity
end
