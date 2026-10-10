import Holant.Proofs.Closure.ClosureWeightedPencilSix
import Holant.Proofs.Closure.ClosureSixPortDescent
import Holant.Proofs.Closure.ClosureShiftedWeightedCards

/-! Actual CURRENT weighted source cards supply the complete analytic
twice-order six-port deck. The resulting split is pulled through the SAME
basis and descended to the original coefficient field, with exact partition
ports and source scale one. Analytic extra phases are never current resources. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Tractable Holant.Algebraic Holant.Projective Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) (sameBasis : params.basis=U)
variable (nonstandard : Holant.Marked.SupportAtlas.nonstandard params)

def transformed {n : ℕ} (f : Signature (OI.K G) n) : Signature Scalar n :=
  U.symm.action (ClosureShiftedWeighted.RH.mapSignature (algebraicEmbedding G) f)

include params sameBasis nonstandard in
theorem current_weighted_matching (q : Signature Scalar 4)
    (actual : ClosureShiftedWeighted.WeightedProduct G P torsion U N q) :
    q=0 ∨ WeightedMatching N.m (delta params) q := by
  rcases actual with zero | ⟨M,_,scalar,c,hc,equation,factors⟩
  · exact Or.inl zero
  · let A := HistorySectorCards.matching (algebraicEmbedding G) U M
    let B : Presentation Scalar (Fin 4) := { A with scalar := c*A.scalar }
    right
    refine ⟨B,mul_ne_zero hc ((map_ne_zero _).mpr scalar),?_,?_⟩
    · intro e
      have h := factors e
      have edge : sectorEdge U=scale params.edgeMultiplier (ClosureShiftedWeighted.D (delta params)) := by
        simpa only [sameBasis] using marked_edge params nonstandard
      rw [edge,scale_mul_right] at h
      exact (ClosureShiftedWeighted.scale_groupM_iff _ _ params.edgeMultiplier_ne_zero _).mp h
    · calc
        q=c • A.tensor := equation
        _=B.tensor := by
          funext x
          simp [B,Presentation.tensor,productValue,mul_assoc]

include params sameBasis nonstandard in
theorem current_weighted_deck (f : Signature (OI.K G) 6)
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    WeightedSixDeck N.m (delta params) (transformed G U f) := by
  intro e p t
  exact current_weighted_matching G P torsion U N params sameBasis nonstandard _
    (ClosureShiftedWeighted.rootCard_weighted G P torsion U N params sameBasis nonstandard f stable e p t)

theorem transformed_nonzero {n : ℕ} (f : Signature (OI.K G) n) (nonzero : f≠0) :
    transformed G U f≠0 := by
  intro zero
  have inverse := U.action_symm_action (ClosureShiftedWeighted.RH.mapSignature (algebraicEmbedding G) f)
  change U.action (transformed G U f)=_ at inverse
  rw [zero,ClosureFactorTreeAction.action_zero] at inverse
  apply nonzero
  funext x
  apply (algebraicEmbedding G).injective
  simpa only [ClosureShiftedWeighted.RH.mapSignature,map_zero,Pi.zero_apply] using (congrFun inverse x).symm

/-- Pull back the exact ambient partition, then normalize the source scale
to one by absorbing the ambient scale into a descended factor. -/
theorem split_to_original {n : ℕ} (f : Signature (OI.K G) n) (nonzero : f≠0)
    {left right : AnySignature ℂ}
    (split : ProperSplit
      (⟨n,ClosureShiftedWeighted.RH.mapSignature ClosureMarkedDihedral.inclusion (transformed G U f)⟩ : AnySignature ℂ)
      left right) :
    ∃ A : Signature (OI.K G) left.1,∃ B : Signature (OI.K G) right.1,
      ∃ result : ProperSplit (⟨n,f⟩ : AnySignature (OI.K G)) ⟨left.1,A⟩ ⟨right.1,B⟩,
        result.ports=split.ports ∧ result.scale=1 := by
  obtain ⟨A,B,algebraic,ports,_⟩ := ClosureSixPort.exact_split_descent
    ClosureMarkedDihedral.inclusion ⟨n,transformed G U f⟩ (transformed_nonzero G U f nonzero) split
  let originalMapped : ProperSplit
      (mapSignature (algebraicEmbedding G) (⟨n,f⟩ : AnySignature (OI.K G)))
      (ClosureFactorTreeAction.signature U ⟨left.1,A⟩)
      (ClosureFactorTreeAction.signature U ⟨right.1,B⟩) := by
    let acted := ClosureFactorTreeAction.split U algebraic
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
  obtain ⟨C,D,original,exactPorts,unit⟩ := ClosureSixPort.exact_split_descent
    (algebraicEmbedding G) ⟨n,f⟩ nonzero originalMapped
  exact ⟨C,D,original,exactPorts.trans ports,unit⟩

include params sameBasis nonstandard in
/-- Actual CURRENT weighted stability yields a genuine original-field
1+5 or 2+4 split. No classifier, gauge, extra root deck or factor is input. -/
theorem current_six_split (range : 4≤N.m) (f : Signature (OI.K G) 6) (nonzero : f≠0)
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    ∃ left right : AnySignature (OI.K G),
      ((left.1=1 ∧ right.1=5) ∨ (left.1=2 ∧ right.1=4)) ∧
      ∃ result : ProperSplit (⟨6,f⟩ : AnySignature (OI.K G)) left right,result.scale=1 := by
  obtain ⟨left,right,arity,⟨split⟩⟩ := weighted_six_split range (delta params)
    (delta_ne_zero params) (delta_root params) (transformed G U f)
    (transformed_nonzero G U f nonzero)
    (current_weighted_deck G P torsion U N params sameBasis nonstandard f stable)
  obtain ⟨A,B,result,_,unit⟩ := split_to_original G U f nonzero split
  exact ⟨⟨left.1,A⟩,⟨right.1,B⟩,arity,result,unit⟩

include params sameBasis nonstandard in
theorem current_six_not_prime (range : 4≤N.m) (f : Signature (OI.K G) 6) (nonzero : f≠0)
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    ¬Prime (⟨6,f⟩ : AnySignature (OI.K G)) := by
  obtain ⟨left,right,_,split,_⟩ := current_six_split G P torsion U N params sameBasis nonstandard range f nonzero stable
  exact fun prime => prime.2 ⟨left,right,⟨split⟩⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
