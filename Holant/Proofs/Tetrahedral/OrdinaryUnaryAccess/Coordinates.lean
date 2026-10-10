import Holant.Proofs.Tetrahedral.OrdinaryReplication.Source
import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist
import Holant.Proofs.Reductions.FactorSaturation.PrefixMachine
import Holant.EightVertex.ProductAnchor.TemplateTransport
import Holant.Proofs.Algorithms.QuaternaryUnaryAccess


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.TetrahedralCompletion.OrdinaryUnaryAccess
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution UniversalPairReduction
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.Hardness.GeneralExtraction GeneralPowerExposure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace Anchor
export Holant.LocalDrafts.MainChain.QuaternaryAnchorAccess
  (K presentation matrix inverse inverse_matrix kappa kappa_ne pulled_edge arity)
end Anchor
namespace Companion
export Holant.LocalDrafts.MainChain.QuaternaryOrdinaryCompanion (decoded decoded_eq4)
end Companion
namespace Pair
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication
  (pinPair anchorInputEncoding anchorValue access accessOriginalL)
end Pair

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (A : QuaternaryEqualityTerminal.AnchorStep (FiniteFamily.family G))
abbrev K := Anchor.K G A
abbrev F := Anchor.presentation G A
local instance : Algebra ℚ (K G A) := (K G A).algebra'
local instance : CharZero (K G A) := Algebra.charZero_of_charZero ℚ (K G A)

def pin (j : Bool) : Signature (K G A) 1 := fun x => if x 0=j then 1 else 0
def unary (j : Bool) : Signature (K G A) 1 := fun x => Anchor.inverse G A (x 0) j

/-- This is the original, not an arbitrarily conjugate, matrix inverse. -/
theorem matrix_inverse : Kernel.mul (Anchor.matrix G A) (Anchor.inverse G A)=Signature.equality := by
  funext b c
  apply Subtype.val_injective
  have h := congrFun (congrFun A.basis.matrix_inverse b) c
  cases b <;> cases c <;>
    simpa [Kernel.mul,Fintype.sum_bool,QuaternaryAnchorAccess.matrix,
      QuaternaryAnchorAccess.inverse,fieldCoefficient,QuaternaryAnchorAccess.values,
      Signature.equality] using h

theorem action_inverse_pin (j : Bool) :
    Signature.coordinateAction (fun _ => Anchor.inverse G A) (pin G A j)=unary G A j := by
  have hp : pin G A j=fun x => if x=(fun _ => j) then 1 else 0 := by
    funext x
    simp [pin,funext_iff,Fin.forall_fin_succ]
  rw [hp]
  funext x
  simp [Signature.coordinateAction,unary,Fin.prod_univ_one]

theorem action_unary (j : Bool) :
    Signature.coordinateAction (fun _ => Anchor.matrix G A) (unary G A j)=pin G A j := by
  rw [←action_inverse_pin]
  exact Signature.coordinateAction_cancel _ _ (fun _ => matrix_inverse G A) _

/-- Both coefficients are actually in the old work field. No new square
root, extension, or hypothesis that a coordinate matrix belongs to L. -/
theorem two_entries (j : Bool) :
    (2 : K G A)*Anchor.inverse G A false j*Anchor.inverse G A true j=Anchor.kappa G A := by
  have h := congrFun (congrFun (Anchor.pulled_edge G A) j) j
  have h' : Anchor.inverse G A false j*Anchor.inverse G A true j+
      Anchor.inverse G A false j*Anchor.inverse G A true j=Anchor.kappa G A := by
    simpa [Kernel.pullback,Kernel.mul,Kernel.transpose,Signature.disequality,
      Signature.equality,Fintype.sum_bool,mul_comm] using h
  linear_combination h'

theorem unary_entry_nonzero (j b : Bool) : unary G A j (fun _ => b)≠0 := by
  have h := two_entries G A j
  cases b <;> intro hz <;> simp only [unary] at hz <;>
    apply Anchor.kappa_ne G A <;> simpa [hz] using h.symm

theorem unary_nonzero (j : Bool) : unary G A j≠0 := by
  intro h
  exact unary_entry_nonzero G A j false (congrFun h (fun _ => false))

def parent (j : Bool) : Signature (K G A) 2 := Signature.tensor (unary G A j) (unary G A j)

theorem action_pair (j : Bool) :
    Signature.coordinateAction (fun _ => Anchor.inverse G A)
      (fun x : Fin 2 → Bool => Pair.pinPair (K:=K G A) j (x 0) (x 1))=parent G A j := by
  have hp : (fun x : Fin 2 → Bool => Pair.pinPair (K:=K G A) j (x 0) (x 1))=
      Signature.tensor (pin G A j) (pin G A j) := by
    funext x
    simp [Pair.pinPair,Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.pinPair,
      pin,Signature.tensor_apply]
  rw [hp]
  simpa only [action_inverse_pin,parent] using
    Holant.EightVertex.ProductAnchor.coordinateAction_tensor
      (Anchor.inverse G A) (pin G A j) (pin G A j)

theorem parent_nonzero (j : Bool) : parent G A j≠0 := by
  intro h
  have hh := congrFun h (fun _ => false)
  apply mul_ne_zero (unary_entry_nonzero G A j false) (unary_entry_nonzero G A j false)
  simpa [parent,Signature.tensor_apply] using hh

/-- The NEW known pair has a specified original-order split; no existing
stored q/tree is reselected and no existential saturation witness is used. -/
def split (j : Bool) : ProperSplit (⟨2,parent G A j⟩ : AnySignature (K G A))
    ⟨1,unary G A j⟩ ⟨1,unary G A j⟩ where
  left_pos := by norm_num
  right_pos := by norm_num
  ports := finSumFinEquiv
  scale := 1
  equation := by
    funext x
    simp [parent,Signature.tensor_apply,unary,finSumFinEquiv]

abbrev pairArity := extendedArity (s+1) (Anchor.arity G A)
def arity (i : ℕ) : ℕ := if i<s+2 then pairArity G A i else 1
def originalPair (j : Bool) := BinaryFamily.signatures (Companion.decoded G A) (Pair.pinPair (K:=K G A) j)

theorem base_arity (i : Fin (s+2)) : arity G A i.val=pairArity G A i.val := by
  simp [arity,i.isLt]

/-- The full ordinary table is the SAME RG+Eq4+pair, then one unary slot.
Total arity beyond the valid old range changes only to accommodate that slot. -/
def ordinaryTable (j : Bool) (i : ℕ) : Signature (K G A) (arity G A i) :=
  if hi : i<s+2 then
    fun x => originalPair G A j ⟨i,hi⟩ (fun k => x (Fin.cast (base_arity G A ⟨i,hi⟩).symm k))
  else fun x => pin G A j (fun k => x (Fin.cast (by simp [arity,hi]) k))
def nativeTable (j : Bool) (i : ℕ) : Signature (K G A) (arity G A i) :=
  Signature.coordinateAction (fun _ => Anchor.inverse G A) (ordinaryTable G A j i)

abbrev ordinaryFamily (j : Bool) (n : ℕ) :=
  FactorSaturation.PrefixMachine.family (s:=s+2) (ordinaryTable G A j) n
abbrev family (j : Bool) (n : ℕ) :=
  FactorSaturation.PrefixMachine.family (s:=s+2) (nativeTable G A j) n

theorem forward (j : Bool) (i : ℕ) :
    Signature.coordinateAction (fun _ => Anchor.matrix G A) (nativeTable G A j i)=
      ordinaryTable G A j i :=
  Signature.coordinateAction_cancel _ _ (fun _ => matrix_inverse G A) _

private theorem signature_cast_sigma {K : Type*} {m n : ℕ} (h : m=n)
    (f : Signature K m) :
    (⟨n,fun x => f (fun k => x (Fin.cast h k))⟩ : AnySignature K)=⟨m,f⟩ := by
  subst n
  rfl

private def nativeAny (f : AnySignature (K G A)) : AnySignature (K G A) :=
  ⟨f.1,Signature.coordinateAction (fun _ => Anchor.inverse G A) f.2⟩

theorem ordinary_parent_label (j : Bool) :
    (⟨arity G A (s+1),ordinaryTable G A j (s+1)⟩ : AnySignature (K G A))=
      ⟨2,fun x => Pair.pinPair (K:=K G A) j (x 0) (x 1)⟩ := by
  have hs : s+1<s+2 := by omega
  change (⟨arity G A (s+1),ordinaryTable G A j (s+1)⟩ : AnySignature (K G A))=_
  simp only [ordinaryTable,dif_pos hs]
  apply (signature_cast_sigma (base_arity G A ⟨s+1,hs⟩).symm
    (originalPair G A j ⟨s+1,hs⟩)).trans
  unfold originalPair BinaryFamily.signatures
  simp only [Fin.val_mk,dif_neg (Nat.lt_irrefl (s+1))]
  exact signature_cast_sigma (m:=2) (n:=pairArity G A (s+1)) (by simp [pairArity,extendedArity])
    (fun x => Pair.pinPair (K:=K G A) j (x 0) (x 1))

theorem parent_label (j : Bool) :
    (⟨arity G A (s+1),family G A j 0 ⟨s+1,by omega⟩⟩ : AnySignature (K G A))=
      ⟨2,parent G A j⟩ := by
  have h := congrArg (nativeAny G A) (ordinary_parent_label G A j)
  simpa only [nativeAny,action_pair,family,FactorSaturation.PrefixMachine.family,nativeTable] using h

theorem parent_member (j : Bool) : (⟨2,parent G A j⟩ : AnySignature (K G A))∈
    Set.range (fun i => (⟨arity G A i.val,family G A j 0 i⟩ : AnySignature (K G A))) :=
  ⟨⟨s+1,by omega⟩,parent_label G A j⟩

/-- BOTH native charge signs come from this actual transported pair. The
ordinary pure pair is not used as a native mixed-support witness. -/
theorem mixedSupport (j : Bool) : GeneralCarrierExistence.MixedSupport
    (Set.range (fun i => (⟨arity G A i.val,family G A j 0 i⟩ : AnySignature (K G A)))) := by
  intro b
  refine ⟨2,parent G A j,parent_member G A j,(fun _ => b),?_,?_⟩
  · simpa [parent,Signature.tensor_apply] using
      mul_ne_zero (unary_entry_nonzero G A j b) (unary_entry_nonzero G A j b)
  · norm_num [Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.balance]

/-- This actual parent is already the exact ordered second power. Hence
no auxiliary carrier or new physical vertex needs to be selected here. -/
theorem parent_power (j : Bool) : parent G A j=Carrier.blockPower (unary G A j) 2 := by
  funext x
  simp [parent,Signature.tensor_apply,Carrier.blockPower,unary,
    Fin.prod_univ_succ,finProdFinEquiv]

def powerNetwork (j : Bool) : Network (K G A) (2*1) := Network.corolla (parent G A j)
def powerLabels (j : Bool) : Labelling (powerNetwork G A j).shape (s+2) 1 (arity G A) where
  vertex _ := ⟨s+1,by omega⟩
  vertex_arity _ := congrArg Sigma.fst (parent_label G A j)
  edge := Fin.elim0

/-- Actual one-vertex macro over the SAME pair label, exponent 2 and unit
scalar. It is a two-port tensor-power realization, not a unary realization.
Arbitrary unary occurrences are subsequently handled by the real 2.16
residue/grouping interpreter, including its live/dead anchor correction. -/
def unaryPower (j : Bool) : PowerMacro (family G A j 0) (unary G A j) where
  exponent := 2
  positive := by decide
  scale := 1
  scale_ne_zero := one_ne_zero
  network := powerNetwork G A j
  labels := powerLabels G A j
  value := by
    rw [Labelling.denote_template]
    have hn : ((powerLabels G A j).sourceNetwork (family G A j 0)
        (fun _ : Fin 1 => Signature.disequality)).denote=(powerNetwork G A j).denote := by
      apply Network.denote_congr
      · intro v x
        exact Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
          (family G A j 0 ⟨s+1,by omega⟩) (parent G A j) (parent_label G A j)
          (congrArg Sigma.fst (parent_label G A j)) x
      · intro e b c
        exact Fin.elim0 e
    rw [hn]
    change (Network.corolla (parent G A j)).denote = _
    rw [Network.denote_corolla,parent_power]
    simp

theorem power_exponent (j : Bool) : (unaryPower G A j).exponent=2 := rfl
theorem power_scale (j : Bool) : (unaryPower G A j).scale=1 := rfl
theorem power_vertices (j : Bool) : (unaryPower G A j).network.shape.vertices=1 := rfl
theorem power_edges (j : Bool) : (unaryPower G A j).network.shape.edges=0 := rfl
theorem power_port (j : Bool) (i : Fin 2) :
    (unaryPower G A j).network.shape.ports ⟨⟨0,by change 0<1; decide⟩,i⟩=Sum.inl i := rfl

theorem ordinary_next_label (j : Bool) :
    (⟨arity G A (s+2),ordinaryTable G A j (s+2)⟩ : AnySignature (K G A))=
      ⟨1,pin G A j⟩ := by
  simp only [ordinaryTable,dif_neg (Nat.lt_irrefl (s+2))]
  exact signature_cast_sigma (by simp [arity]) (pin G A j)

theorem next_label (j : Bool) :
    (⟨arity G A (s+2),nativeTable G A j (s+2)⟩ : AnySignature (K G A))=
      ⟨1,unary G A j⟩ := by
  have h := congrArg (nativeAny G A) (ordinary_next_label G A j)
  simpa only [nativeAny,nativeTable,action_inverse_pin] using h

def nextPower (j : Bool) (i : Fin 1) :
    PowerMacro (family G A j 0) (nativeTable G A j ((s+2)+i.val)) := by
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  simpa only [Fin.val_zero,Nat.add_zero] using
    QuaternaryUnaryAccess.castPower (next_label G A j) (unaryPower G A j)

def chain (j : Bool) : RecursiveMachine.Chain (family G A j 0) (family G A j 1) :=
  FactorSaturation.PrefixMachine.chain (nativeTable G A j) (nextPower G A j) 1 le_rfl

end Holant.LocalDrafts.TetrahedralCompletion.OrdinaryUnaryAccess
