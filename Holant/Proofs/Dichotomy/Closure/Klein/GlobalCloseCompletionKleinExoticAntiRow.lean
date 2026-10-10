import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinExoticPins
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinExoticAntiAlgebra

/-! The actual exotic E₂ row survives the ordinary Eq4/two-pin programme.
Its two nonzero coefficients and exact equal-fourth relation are supplied in
the resulting finite work field; no hypothetical antidiagonal is adjoined. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticAntiRow
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
namespace S
export GlobalCloseCompletionKleinExoticOrdinarySource (retained reps mapped rowLabel row_literal)
end S
namespace D
export GlobalCloseCompletionKleinExoticPins (input data old_included)
end D
namespace A
export GlobalCloseCompletionKleinExoticAntiAlgebra (left right literal left_nonzero right_nonzero squares fourths)
end A
namespace O
export GenericOrdinarySource (field table arity count family)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

private theorem lift_anti {K : Type} [Field K] (phi : K→+*AlgebraicComplex)
    {n : ℕ} (f : Signature K n) (v w : AlgebraicComplex)
    (mapped : RingHomRealization.mapAny phi (⟨n,f⟩ : AnySignature K)=
      ⟨2,NoXWeightedAntiSigned.anti v w⟩) :
    ∃a b : K,phi a=v ∧ phi b=w ∧ (⟨n,f⟩ : AnySignature K)=⟨2,NoXWeightedAntiSigned.anti a b⟩ := by
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

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (exotic : ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic=.exotic)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

abbrev source := D.data G P torsion cardinal noncyclic exotic q core literal stable
abbrev multiplier := (S.reps G P torsion cardinal noncyclic exotic q core literal).multiplier 2

theorem member : (⟨2,NoXWeightedAntiSigned.anti
    (A.left (multiplier G P torsion cardinal noncyclic exotic q core literal))
    (A.right (multiplier G P torsion cardinal noncyclic exotic q core literal))⟩ : AnySignature AlgebraicComplex)∈
    O.family G (source G P torsion cardinal noncyclic exotic q core literal stable) := by
  apply D.old_included G P torsion cardinal noncyclic exotic q core literal stable
  refine ⟨S.rowLabel G P torsion cardinal noncyclic exotic q core literal 2,?_⟩
  refine (S.row_literal G P torsion cardinal noncyclic exotic q core literal 2).trans ?_
  rw [(S.reps G P torsion cardinal noncyclic exotic q core literal).normal_form,A.literal]

structure Output where
  label : Fin (O.count G (source G P torsion cardinal noncyclic exotic q core literal stable))
  left : O.field G (source G P torsion cardinal noncyclic exotic q core literal stable)
  right : O.field G (source G P torsion cardinal noncyclic exotic q core literal stable)
  left_nonzero : left≠0
  right_nonzero : right≠0
  literal : (⟨O.arity G (source G P torsion cardinal noncyclic exotic q core literal stable) label.val,
    O.table G (source G P torsion cardinal noncyclic exotic q core literal stable) label⟩ :
      AnySignature (O.field G (source G P torsion cardinal noncyclic exotic q core literal stable)))=
        ⟨2,NoXWeightedAntiSigned.anti left right⟩
  squares : left^2= -right^2
  fourths : (left : AlgebraicComplex)^4=(right : AlgebraicComplex)^4

def produce : Output G P torsion cardinal noncyclic exotic q core literal stable := Classical.choice (by
  obtain ⟨j,hj⟩ := member G P torsion cardinal noncyclic exotic q core literal stable
  obtain ⟨v,w,hv,hw,lit⟩ := lift_anti (O.field G (source G P torsion cardinal noncyclic exotic q core literal stable)).subtype
    (O.table G (source G P torsion cardinal noncyclic exotic q core literal stable) j) _ _ hj
  have nonzero := (S.reps G P torsion cardinal noncyclic exotic q core literal).multiplier_ne_zero 2
  refine ⟨⟨j,v,w,?_,?_,lit,?_,?_⟩⟩
  · intro zero
    exact A.left_nonzero _ nonzero (hv.symm.trans (by rw [zero,map_zero]))
  · intro zero
    exact A.right_nonzero _ nonzero (hw.symm.trans (by rw [zero,map_zero]))
  · apply (O.field G (source G P torsion cardinal noncyclic exotic q core literal stable)).subtype.injective
    rw [map_pow,map_neg,map_pow,hv,hw]
    exact A.squares _
  · change ((O.field G (source G P torsion cardinal noncyclic exotic q core literal stable)).subtype v)^4=
      ((O.field G (source G P torsion cardinal noncyclic exotic q core literal stable)).subtype w)^4
    exact (congrArg (fun z : AlgebraicComplex=>z^4) hv).trans
      ((A.fourths _).trans (congrArg (fun z : AlgebraicComplex=>z^4) hw).symm))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticAntiRow
end
