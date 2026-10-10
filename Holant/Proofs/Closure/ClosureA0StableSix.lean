import Holant.Proofs.Closure.ClosureA0StableSource
import Holant.Proofs.Closure.ClosureSixPortDescent

/-! Closed A0 six-port exclusion and exact ORIGINAL-field factor pullback.
The root deck, normalization and coefficient descent are constructed from the
actual current source. The chosen ambient split's partition is retained twice,
and the final source split has multiplier one. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureA0Stable
open Holant Holant.Tractable Holant.Algebraic Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Certificates.MatchingContractionClosure
open ClosurePhysicalBridge

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))

abbrev complexTransformed {n : ℕ} (f : Signature (OI.K G) n) : Signature ℂ n :=
  RH.mapSignature ClosureMarkedDihedral.inclusion (transformed G f)

theorem transformed_nonzero {n : ℕ} (f : Signature (OI.K G) n) (nonzero : f≠0) :
    transformed G f≠0 := by
  intro zero
  have recovered := basis.action_symm_action (RH.mapSignature (algebraicEmbedding G) f)
  change basis.action (transformed G f)=_ at recovered
  rw [zero,ClosureFactorTreeAction.action_zero] at recovered
  apply nonzero
  funext x
  apply (algebraicEmbedding G).injective
  simpa only [RH.mapSignature,map_zero,Pi.zero_apply] using (congrFun recovered x).symm

theorem complexTransformed_nonzero {n : ℕ} (f : Signature (OI.K G) n) (nonzero : f≠0) :
    complexTransformed G f≠0 := by
  intro zero
  apply transformed_nonzero G f nonzero
  funext x
  apply ClosureMarkedDihedral.inclusion.injective
  simpa only [RH.mapSignature,map_zero,Pi.zero_apply] using congrFun zero x

set_option backward.isDefEq.respectTransparency false in
/-- The SAME ambient split is pulled through the invertible action and then
back into the original field. The factor arities, exact ordered partition and
unit source multiplier are conclusions. -/
theorem split_to_original {n : ℕ} (f : Signature (OI.K G) n) (nonzero : f≠0)
    {left right : AnySignature ℂ}
    (split : ProperSplit (⟨n,complexTransformed G f⟩ : AnySignature ℂ) left right) :
    ∃ A : Signature (OI.K G) left.1, ∃ B : Signature (OI.K G) right.1,
      ∃ result : ProperSplit (⟨n,f⟩ : AnySignature (OI.K G)) ⟨left.1,A⟩ ⟨right.1,B⟩,
        result.ports=split.ports ∧ result.scale=1 := by
  obtain ⟨A,B,algebraic,ports,unit⟩ := ClosureSixPort.exact_split_descent
    ClosureMarkedDihedral.inclusion ⟨n,transformed G f⟩
    (transformed_nonzero G f nonzero) split
  let originalMapped : ProperSplit
      (mapSignature (algebraicEmbedding G) (⟨n,f⟩ : AnySignature (OI.K G)))
      (ClosureFactorTreeAction.signature basis ⟨left.1,A⟩)
      (ClosureFactorTreeAction.signature basis ⟨right.1,B⟩) := by
    let acted := ClosureFactorTreeAction.split basis algebraic
    exact {
      left_pos := algebraic.left_pos
      right_pos := algebraic.right_pos
      ports := algebraic.ports
      scale := algebraic.scale
      equation := by
        have equation := acted.equation
        simp only [acted,ClosureFactorTreeAction.signature,transformed,
          ClosureFactorTreeAction.split_ports,ClosureFactorTreeAction.split_scale,
          InvertibleKernel.action_symm_action] at equation
        funext x
        have point := congrFun equation x
        change algebraicEmbedding G (f x)=_ at point
        exact point }

  obtain ⟨C,D,original,exactPorts,exactUnit⟩ := ClosureSixPort.exact_split_descent
    (algebraicEmbedding G) ⟨n,f⟩ nonzero originalMapped
  exact ⟨C,D,original,exactPorts.trans ports,exactUnit⟩

include N

/-- Literal CURRENT A0 stability gives an actual original-field 1+5 or 2+4
factor of the given six-port tensor. Zero samples require no separate premise. -/
theorem current_six_split (f : Signature (OI.K G) 6) (nonzero : f≠0)
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g) :
    ∃ left right : AnySignature (OI.K G),
      ((left.1=1 ∧ right.1=5) ∨ (left.1=2 ∧ right.1=4)) ∧
      ∃ split : ProperSplit (⟨6,f⟩ : AnySignature (OI.K G)) left right, split.scale=1 := by
  have deck : ClosureSixPort.OrderedRootDeck N.selected.m (complexTransformed G f) := by
    intro e p t root
    have h := ordered_root_deck G P torsion N f stable e p t root
    simpa only [ClosureCompatibleAlignment.phaseCardN_actual,ClosureSixPort.phaseCard_actual] using h
  obtain ⟨left,right,arity,⟨split⟩⟩ := ClosureSixPort.direct_six_port_split N.selected.range
    (complexTransformed G f) (complexTransformed_nonzero G f nonzero) deck
  obtain ⟨A,B,result,_,unit⟩ := split_to_original G f nonzero split
  exact ⟨⟨left.1,A⟩,⟨right.1,B⟩,arity,result,unit⟩

theorem current_six_not_prime (f : Signature (OI.K G) 6) (nonzero : f≠0)
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g) :
    ¬Prime (⟨6,f⟩ : AnySignature (OI.K G)) := by
  obtain ⟨left,right,_,split,_⟩ := current_six_split G P torsion N f nonzero stable
  exact fun prime => prime.2 ⟨left,right,⟨split⟩⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureA0Stable
end
