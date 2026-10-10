import Holant.Proofs.Closure.ClosureA0StableSelected
import Holant.Proofs.Closure.ClosureA0StableSix
import Holant.Proofs.Closure.ClosureBStableFactor

/-! Closed A0 higher-arity factorization. Every selected presentation,
matching alignment, factor-line bound and fixed edge is derived from the same
CURRENT source deck. No Family/FourProducts/alignment/desired-factor input is
supplied. The original field and exact ordered factor partition are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureA0Stable
open Holant Holant.Tractable Holant.Algebraic Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge ClosureCompatibleAlignment
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.TwoCardLocalization

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))
variable {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4)))
variable (stable : ∀ g ∈ rawDeck P.family torsion f,
  Holant.Certificates.MatchingContractionClosure.MatchingOrZero (actualTransfers P.family) g)

abbrev Sample := ClosureBStableFactor.Sample N.selected.m r (Tensor.reindex order.symm (transformed G f))

def selectedSample (i : Sample G P torsion N f order) :
    SelectedCard G P torsion N f order i.val.1 i.val.2 :=
  selectCard G P torsion N f order i.val.1 i.val.2 stable i.property

variable (anchor : Sample G P torsion N f order)

def familyPorts : (Fin (r+1) × Bool) ≃ Fin (2*r+2) :=
  (selectedSample G P torsion N f order stable anchor).ports

def familyTables (i : Sample G P torsion N f order) : Fin (r+1) → Mat :=
  alignedFactor (familyPorts G P torsion N f order stable anchor)
    (selectedSample G P torsion N f order stable i).ports
    (selectedSample G P torsion N f order stable i).factors

def familyCoefficient (i : Sample G P torsion N f order) : Scalar :=
  (selectedSample G P torsion N f order stable i).algebraic.scalar

theorem family_member (i : Sample G P torsion N f order) (e : Fin (r+1)) :
    familyTables G P torsion N f order stable anchor i e ∈ groupM N.selected.m :=
  alignedFactor_group (by have := N.range; omega) _ _ _
    (selectedSample G P torsion N f order stable i).factors_member e

theorem family_equation (large : 2≤r) (i : Sample G P torsion N f order) :
    Signature.contract (M i.val.1 i.val.2.val) (Tensor.reindex order.symm (transformed G f))=
      MC.productValue (familyPorts G P torsion N f order stable anchor)
        (familyTables G P torsion N f order stable anchor i)
        (familyCoefficient G P torsion N f order stable i) := by
  let A := selectedSample G P torsion N f order stable anchor
  let S := selectedSample G P torsion N f order stable i
  have same := selected_matchings_equal G P torsion N f order large stable
    anchor.val.1 i.val.1 anchor.val.2 i.val.2 A S
  have equation := S.coefficient_product
  rw [←aligned_product A.ports S.ports same S.factors S.algebraic.scalar] at equation
  exact equation

theorem family_distance (large : 2≤r) (i j : Sample G P torsion N f order)
    (e d : Fin (r+1)) (different : e≠d) :
    ProjectivelyEqual (familyTables G P torsion N f order stable anchor j e)
      (familyTables G P torsion N f order stable anchor i e) ∨
    ProjectivelyEqual (familyTables G P torsion N f order stable anchor j d)
      (familyTables G P torsion N f order stable anchor i d) :=
  common_matching_one_step_bound N.selected.range large _
    (fun cut p t => outside_root_cases G P torsion N f stable order cut p t)
    (M i.val.1 i.val.2.val) (M j.val.1 j.val.2.val)
    (familyPorts G P torsion N f order stable anchor)
    (familyTables G P torsion N f order stable anchor i)
    (familyTables G P torsion N f order stable anchor j)
    (familyCoefficient G P torsion N f order stable i)
    (familyCoefficient G P torsion N f order stable j)
    (family_member G P torsion N f order stable anchor i)
    (family_member G P torsion N f order stable anchor j)
    (selectedSample G P torsion N f order stable i).coefficient_nonzero
    (selectedSample G P torsion N f order stable j).coefficient_nonzero
    (family_equation G P torsion N f order stable anchor large i)
    (family_equation G P torsion N f order stable anchor large j) e d different

/-- One actual anchor is selected internally from the nonzero source tensor.
The two-root inversion proof includes all zero samples. -/
def family (nonzero : f≠0) (large : 2≤r) :
    ClosureBStableFactor.Family N.selected.m r (Tensor.reindex order.symm (transformed G f)) := by
  have transformedLive : Tensor.reindex order.symm (transformed G f)≠0 := by
    intro zero
    apply transformed_nonzero G f nonzero
    have h := congrArg (Tensor.reindex order) zero
    funext x
    simpa only [Tensor.reindex,Equiv.apply_symm_apply,Pi.zero_apply] using congrFun h x
  let anchor := ClosureBStableFactor.canonicalAnchor N.selected.range
    (Tensor.reindex order.symm (transformed G f)) transformedLive
  exact ⟨anchor,familyPorts G P torsion N f order stable anchor,
    familyTables G P torsion N f order stable anchor,
    familyCoefficient G P torsion N f order stable,
    family_equation G P torsion N f order stable anchor large,
    family_distance G P torsion N f order stable anchor large⟩

include P torsion N order stable

/-- Actual 2+(n−2) ORIGINAL-field split with multiplier one; the exact
partition from the constructed fixed edge is pulled through the same order. -/
theorem current_higher_split (nonzero : f≠0) (large : 2≤r) :
    ∃ A : Signature (OI.K G) 2, ∃ B : Signature (OI.K G) (2*r+2),
      ∃ result : ProperSplit (⟨2*r+4,f⟩ : AnySignature (OI.K G)) ⟨2,A⟩ ⟨2*r+2,B⟩,
        result.scale=1 := by
  let F := family G P torsion N f order stable nonzero large
  obtain ⟨edge,R,s,partition,unit⟩ := F.split N.selected.range large
  let left : AnySignature Scalar := ⟨2,kernelSignature (F.tables F.anchor edge)⟩
  let right : AnySignature Scalar := ⟨2*r+2,R⟩
  let originalOrder : ProperSplit (⟨2*r+4,transformed G f⟩ : AnySignature Scalar) left right := {
    left_pos := s.left_pos
    right_pos := s.right_pos
    ports := s.ports.trans order
    scale := s.scale
    equation := by
      have h := congrArg (Tensor.reindex order) s.equation
      funext x
      simpa only [Tensor.reindex,Equiv.trans_apply,Equiv.apply_symm_apply] using congrFun h x }
  let complexSplit : ProperSplit (⟨2*r+4,complexTransformed G f⟩ : AnySignature ℂ)
      (mapSignature ClosureMarkedDihedral.inclusion left)
      (mapSignature ClosureMarkedDihedral.inclusion right) := originalOrder.map ClosureMarkedDihedral.inclusion
  obtain ⟨A,B,result,exactPorts,exactUnit⟩ := split_to_original G f nonzero complexSplit
  exact ⟨A,B,result,exactUnit⟩

theorem current_higher_not_prime (large : 2≤r) :
    ¬Prime (⟨2*r+4,f⟩ : AnySignature (OI.K G)) := by
  intro prime
  obtain ⟨A,B,result,_⟩ := current_higher_split G P torsion N f order stable prime.1 large
  exact prime.2 ⟨⟨2,A⟩,⟨2*r+2,B⟩,⟨result⟩⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureA0Stable
end
