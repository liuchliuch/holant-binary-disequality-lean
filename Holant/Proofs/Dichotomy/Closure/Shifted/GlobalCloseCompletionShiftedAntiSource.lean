import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedExplicitAnchor
import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedAntiPhase
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned

/-! Literal full weighted-anti rows in one fixed ordinary Eq4/pins source.
The rows are obtained from the real original-field retained catalogue. Their
exact two coefficients descend through the same source-field embedding; no
coordinate-normalized binary is asserted to be a native gadget. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedAntiSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GlobalCloseCompletionShiftedExplicitAnchor
  (basis root root_nonzero root_square retained current finiteAnchor field presentation count arity table data)
end E
namespace PhaseOrder
export GlobalCloseCompletionShiftedAntiPhase (selected primitivePhase outside_four_eighth_failure)
end PhaseOrder
namespace O
export GenericOrdinarySource (field arity table count family)
end O

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (native : GlobalCloseCompletionShiftedMarking.Native G P torsion)
abbrev selected := PhaseOrder.selected G P torsion native
abbrev phaseIndex (t : Phase (selected G P torsion native).m) :=
  HistorySectorNormalized.phaseIndex G P torsion native.reflection.basis
    (selected G P torsion native) true t
abbrev originalBinary (t : Phase (selected G P torsion native).m) :=
  actualRepresentative P.family torsion (phaseIndex G P torsion native t).key
abbrev ambientBinary (t : Phase (selected G P torsion native).m) :=
  (originalBinary G P torsion native t).map (ClosureSourceRows.embedding G)
def left (t : Phase (selected G P torsion native).m) : AlgebraicComplex :=
  -imaginaryUnit*(phaseIndex G P torsion native t).multiplier*t.val/native.reflection.square
def right (t : Phase (selected G P torsion native).m) : AlgebraicComplex :=
  imaginaryUnit*(phaseIndex G P torsion native t).multiplier*native.reflection.square

theorem left_nonzero (t : Phase (selected G P torsion native).m) : left G P torsion native t≠0 :=
  div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr imaginaryUnit_ne_zero)
    (phaseIndex G P torsion native t).nonzero) (t.property.ne_zero (by have := (selected G P torsion native).range; omega)))
    native.reflection.square_nonzero

theorem right_nonzero (t : Phase (selected G P torsion native).m) : right G P torsion native t≠0 :=
  mul_ne_zero (mul_ne_zero imaginaryUnit_ne_zero (phaseIndex G P torsion native t).nonzero)
    native.reflection.square_nonzero

theorem transformed_anti (t : Phase (selected G P torsion native).m) :
    E.basis.action (kernelSignature (ambientBinary G P torsion native t))=
      NoXWeightedAntiSigned.anti (left G P torsion native t) (right G P torsion native t) := by
  exact GlobalCloseCompletionShiftedAntiAlgebra.normalization_anti
    native.reflection.square E.root (phaseIndex G P torsion native t).multiplier t.val
    native.reflection.square_nonzero E.root_nonzero E.root_square
    (ambientBinary G P torsion native t) (phaseIndex G P torsion native t).transfer

theorem ratio (t : Phase (selected G P torsion native).m) :
    left G P torsion native t/right G P torsion native t= -native.reflection.eta*t.val := by
  calc
    _ = -t.val/native.reflection.square^2 := by
      unfold left right
      field_simp [imaginaryUnit_ne_zero,(phaseIndex G P torsion native t).nonzero,native.reflection.square_nonzero]
    _ = _ := by
      rw [native.reflection.square_eq]
      field_simp [native.reflection.eta_nonzero]

variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)
abbrev source := E.data G P torsion native q core literal stable
local instance : Algebra ℚ (O.field G (source G P torsion native q core literal stable)) :=
  (O.field G (source G P torsion native q core literal stable)).algebra'

theorem anti_member (t : Phase (selected G P torsion native).m) :
    (⟨2,NoXWeightedAntiSigned.anti (left G P torsion native t) (right G P torsion native t)⟩ :
      AnySignature AlgebraicComplex)∈O.family G (source G P torsion native q core literal stable) := by
  change _∈StableHigherCurrentOrdinarySourceTerminal.physicalFamily G
    (E.retained G P torsion q core literal) (E.finiteAnchor G P torsion native q core literal stable)
  rw [StableHigherCurrentOrdinarySourceTerminal.physical_family_exact]
  apply Or.inl; apply Or.inl; apply Or.inl
  refine ⟨⟨2,kernelSignature (ambientBinary G P torsion native t)⟩,?_,?_⟩
  · change (⟨2,kernelSignature (ambientBinary G P torsion native t)⟩ : AnySignature AlgebraicComplex)∈
      UniversalPairReduction.FiniteFamily.family
        (StableHigherCurrentPurePinsCore.mapped G (E.retained G P torsion q core literal))
    rw [←StableHigherCurrentFamilyTransport.ambientFamily_eq]
    exact ClosureSourceRows.representative_ambient_retained G P torsion q core literal (by decide)
      (phaseIndex G P torsion native t).key
  · exact congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
      (transformed_anti G P torsion native t)

private theorem lift_anti {K : Type} [Field K] (phi : K→+*AlgebraicComplex)
    {n : ℕ} (f : Signature K n) (v w : AlgebraicComplex)
    (mapped : RingHomRealization.mapAny phi (⟨n,f⟩ : AnySignature K)=
      ⟨2,NoXWeightedAntiSigned.anti v w⟩) :
    ∃ a b : K,phi a=v ∧ phi b=w ∧ (⟨n,f⟩ : AnySignature K)=⟨2,NoXWeightedAntiSigned.anti a b⟩ := by
  have hn : n=2 := congrArg Sigma.fst mapped
  subst n
  have hf : RingHomRealization.mapSignature phi f=NoXWeightedAntiSigned.anti v w :=
    eq_of_heq (Sigma.mk.inj_iff.mp mapped).2
  have hv : phi (f ![false,true])=v := by
    simpa [RingHomRealization.mapSignature,NoXWeightedAntiSigned.anti] using congrFun hf ![false,true]
  have hw : phi (f ![true,false])=w := by
    simpa [RingHomRealization.mapSignature,NoXWeightedAntiSigned.anti] using congrFun hf ![true,false]
  refine ⟨f ![false,true],f ![true,false],hv,hw,?_⟩
  apply congrArg (fun g : Signature K 2=>(⟨2,g⟩ : AnySignature K))
  funext x
  apply phi.injective
  have h := congrFun hf x
  change phi (f x)=_ at h
  refine h.trans ?_
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [NoXWeightedAntiSigned.anti,h0,h1,hv,hw]

structure Row (t : Phase (selected G P torsion native).m) where
  label : Fin (O.count G (source G P torsion native q core literal stable))
  left : O.field G (source G P torsion native q core literal stable)
  right : O.field G (source G P torsion native q core literal stable)
  left_value : (left : AlgebraicComplex)=GlobalCloseCompletionShiftedAntiSource.left G P torsion native t
  right_value : (right : AlgebraicComplex)=GlobalCloseCompletionShiftedAntiSource.right G P torsion native t
  literal : (⟨O.arity G (source G P torsion native q core literal stable) label.val,
    O.table G (source G P torsion native q core literal stable) label⟩ :
      AnySignature (O.field G (source G P torsion native q core literal stable)))=
        ⟨2,NoXWeightedAntiSigned.anti left right⟩

def row (t : Phase (selected G P torsion native).m) : Row G P torsion native q core literal stable t :=
  Classical.choice (by
    obtain ⟨i,hi⟩ := anti_member G P torsion native q core literal stable t
    obtain ⟨v,w,hv,hw,he⟩ := lift_anti
      (O.field G (source G P torsion native q core literal stable)).subtype
      (O.table G (source G P torsion native q core literal stable) i)
      (left G P torsion native t) (right G P torsion native t) hi
    exact ⟨⟨i,v,w,hv,hw,he⟩⟩)

theorem row_left_nonzero (t : Phase (selected G P torsion native).m) :
    (row G P torsion native q core literal stable t).left≠0 := by
  intro zero
  apply left_nonzero G P torsion native t
  exact (row G P torsion native q core literal stable t).left_value.symm.trans (by rw [zero]; rfl)

theorem row_right_nonzero (t : Phase (selected G P torsion native).m) :
    (row G P torsion native q core literal stable t).right≠0 := by
  intro zero
  apply right_nonzero G P torsion native t
  exact (row G P torsion native q core literal stable t).right_value.symm.trans (by rw [zero]; rfl)

theorem row_eighth_ratio (t : Phase (selected G P torsion native).m)
    (eighth : (row G P torsion native q core literal stable t).left^8=
      (row G P torsion native q core literal stable t).right^8) :
    (-native.reflection.eta*t.val)^8=1 := by
  have h := congrArg (fun z : O.field G (source G P torsion native q core literal stable)=>(z : AlgebraicComplex)) eighth
  change ((row G P torsion native q core literal stable t).left : AlgebraicComplex)^8=
    ((row G P torsion native q core literal stable t).right : AlgebraicComplex)^8 at h
  rw [(row G P torsion native q core literal stable t).left_value,
    (row G P torsion native q core literal stable t).right_value] at h
  rw [←ratio G P torsion native t,div_pow,h,div_self (pow_ne_zero 8 (right_nonzero G P torsion native t))]

theorem outside_four_bad_row (notFour : (selected G P torsion native).m≠4) :
    ∃t : Phase (selected G P torsion native).m,
      (t=phaseOne _ ∨ t=PhaseOrder.primitivePhase G P torsion native) ∧
      (row G P torsion native q core literal stable t).left^8≠
        (row G P torsion native q core literal stable t).right^8 := by
  rcases PhaseOrder.outside_four_eighth_failure G P torsion native notFour with first|second
  · refine ⟨phaseOne _,Or.inl rfl,?_⟩
    intro h
    apply first
    simpa only [phaseOne,mul_one] using row_eighth_ratio G P torsion native q core literal stable (phaseOne _) h
  · exact ⟨PhaseOrder.primitivePhase G P torsion native,Or.inr rfl,
      fun h=>second (row_eighth_ratio G P torsion native q core literal stable _ h)⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedAntiSource
end
