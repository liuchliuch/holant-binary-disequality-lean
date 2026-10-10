import Holant.Proofs.Closure.ClosureMarkedShiftParameters
import Holant.Proofs.Closure.ClosureMarkedDihedralA0Resources
import Holant.Proofs.Closure.ClosureMarkedDihedralB
import Holant.Proofs.Closure.ClosureFieldBridgeEquiv

/-! NEW POST-RECOVERY SOURCE; awaiting strict verification after the physical
history capstone. Closed original-family marked routing: all coordinate and
phase data comes from the internally produced actual group. Small orders and
semantic Platonic models are real explicit alternatives, without complexity
upgrades or an assumed successful marked selector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedSourceRouting
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open ClosureMarkedDihedral.Source
open ClosureMarkedShiftConjugator.Reflection
open ClosureMarkedShiftParameters.Reflection
variable {L : Type*} [Field L] [NumberField L]

/-- These payloads refer to the actual source group or its explicitly
constructed semantic index-at-most-two overgroup. No basis is an oracle label. -/
inductive Marking (phi : L →+* Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F) : Type _
  | smallTwo (cardinal : Nat.card (group phi F torsion) = 2)
  | smallFour (cardinal : Nat.card (group phi F torsion) = 4)
      (noncyclic : ¬ IsCyclic (group phi F torsion))
  | cyclic (selected : ClosureMarkedCyclic.NativeCyclic (group phi F torsion))
  | monomial (selected : ClosureMarkedDihedral.NativeM (group phi F torsion))
  | bilinear (selected : ClosureMarkedDihedralB.NativeB (group phi F torsion))
  | unshifted (nativeZ : zClass ∈ group phi F torsion)
      (selected : ClosureMarkedDihedralA0.NativeA0 (group phi F torsion))
      (sourceY : ClosureMarkedDihedralA0Resources.YResource phi F torsion nativeZ)
  | shifted (axis : group phi F torsion ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
      (noncyclic : ¬ IsCyclic (group phi F torsion))
      (notTwo : Nat.card (group phi F torsion) ≠ 2)
      (notFour : Nat.card (group phi F torsion) ≠ 4)
      (noZ : zClass ∉ group phi F torsion)
      (reflection : ClosureMarkedShiftReflection.Reflection phi F torsion)
      (sameSource : reflection = ClosureMarkedShiftReflection.select phi F torsion axis noncyclic)
  | platonic (p : Holant.Certificates.MatchingProductBridge.PlatonicModel)
      (semanticModel : HasModel (ClosureMarkedReversalOvergroup.Ambient.overgroup phi F torsion)
        (.platonic p))

/-- The actual constructed coordinate basis for the non-small native branches.
Small groups and semantic Platonic models retain their separate local boundary. -/
def Marking.basis {phi : L →+* Scalar} {F : SignatureFamily L} {torsion : ResidualTorsion F} :
    Marking phi F torsion → Option InvertibleKernel
  | .smallTwo _ => none
  | .smallFour _ _ => none
  | .cyclic _ => some ClosureMarkedCyclic.basis
  | .monomial _ => some InvertibleKernel.identity
  | .bilinear _ => some basisB
  | .unshifted _ _ _ => some ClosureMarkedDihedralA0.basis
  | .shifted _ _ _ _ _ reflection _ => some reflection.basis
  | .platonic _ _ => none

/-- Standard marked parameters are actually constructed where the dictionary
has them. Cyclic and unshifted branches keep their distinct exact payloads. -/
def Marking.parameters {phi : L →+* Scalar} {F : SignatureFamily L}
    {torsion : ResidualTorsion F}
    (equality : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F) :
    Marking phi F torsion → Option (Σ m : ℕ, Parameters m)
  | .smallTwo _ => none
  | .smallFour _ _ => none
  | .cyclic _ => none
  | .monomial selected => some ⟨selected.m,selected.parameters⟩
  | .bilinear selected => some ⟨selected.selected.m,selected.parameters⟩
  | .unshifted _ _ _ => none
  | .shifted axis _ notTwo notFour noZ reflection _ =>
      some ⟨(reflection.selected axis notTwo notFour).m,
        reflection.parameters equality axis notTwo notFour noZ⟩
  | .platonic _ _ => none

/-- The only inputs are the original embedding, actual residual-torsion family
and retained literal equality. Classification, native axis, small-cardinal
routing, reflection key, phase, square root and model are all selected here. -/
def produce (phi : L →+* Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (equality : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F) :
    Marking phi F torsion := by
  classical
  let H := group phi F torsion
  letI : Finite H := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding phi) F torsion
  if h2 : Nat.card H = 2 then
    exact .smallTwo h2
  else if hc : IsCyclic H then
    have hr : 4 ≤ Nat.card H := by
      rcases ClosureMarkedCyclic.native_cyclic_range H (nativeX_mem phi F torsion equality) with hh | hh
      · exact (h2 hh).elim
      · exact hh
    exact .cyclic (ClosureMarkedCyclic.Source.nativeCyclic phi F torsion equality hc
      (by change 3 ≤ Nat.card H; omega))
  else if h4 : Nat.card H = 4 then
    exact .smallFour h4 hc
  else
    cases ClosureMarkedReversalRouting.Source.route phi F torsion equality with
    | axis a centralizes m range model =>
        have ha := ClosureMarkedReversalRouting.Source.actual_axis phi F torsion a centralizes
        cases a with
        | X =>
            change H ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)) at ha
            if hz : zClass ∈ H then
              exact .unshifted hz (ClosureMarkedDihedralA0.Source.nativeA0 phi F torsion equality ha hz h2 h4)
                (ClosureMarkedDihedralA0Resources.sourceY phi F torsion hz)
            else
              exact .shifted ha hc h2 h4 hz (ClosureMarkedShiftReflection.select phi F torsion ha hc) rfl
        | Z =>
            change H ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) at ha
            exact .monomial (ClosureMarkedDihedral.Source.nativeM phi F torsion equality ha h2 h4)
        | XZ =>
            change H ≤ Subgroup.centralizer ({xClass*zClass} : Set (PGL2 ℂ)) at ha
            exact .bilinear (ClosureMarkedDihedralB.Source.nativeB phi F torsion equality ha h2 h4)
    | platonic p model => exact .platonic p model

/-- The genuine small-four branch supplies the original-field guards needed
by the independently constructed native Klein-four producer. -/
theorem smallFour_source (phi : L →+* Scalar) (F : SignatureFamily L)
    (torsion : ResidualTorsion F) (cardinal : Nat.card (group phi F torsion) = 4)
    (noncyclic : ¬ IsCyclic (group phi F torsion)) :
    Nat.card (completeGroup F torsion) = 4 ∧ ¬ IsCyclic (completeGroup F torsion) :=
  ⟨(source_cardinal phi F torsion).symm.trans cardinal,
    ClosureFieldBridgeEquiv.source_not_isCyclic phi F torsion noncyclic⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedSourceRouting
end
