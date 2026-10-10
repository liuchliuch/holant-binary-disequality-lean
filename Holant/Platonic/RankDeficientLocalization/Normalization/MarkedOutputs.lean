import Holant.Platonic.RankDeficientLocalization.Normalization.MarkedAssembly
import Holant.Platonic.RankDeficientLocalization.Normalization.ActualRepresentatives

/-! Literal O′ outputs in the original current coordinates.  All normalization
and correction factors are actual O′ directions on the original ordinary graph. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.RainbowLocalization.Physical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000


def SixDressing.correctedNetwork (D : SixDressing) (C : Legs) (h : Signature ℂ 6) : Network ℂ 4 :=
  OctahedralSeparator.Native.orderedDressedNetwork D.finalOrder h D.finalKernel
    (fun j => C j*D.finalLegs j)

theorem SixDressing.correctedNetwork_denote (D : SixDressing) (C : Legs) (h : Signature ℂ 6) :
    (D.correctedNetwork C h).denote=act C (Signature.contract Q0
      (Tensor.reindex (TetrahedralDeck.portOrder 1).symm (D.tensor h))) := by
  calc
    (D.correctedNetwork C h).denote=act C (D.network h).denote := by
      rw [SixDressing.correctedNetwork,SixDressing.network,
        OctahedralSeparator.Native.orderedDressedNetwork_denote,
        OctahedralSeparator.Native.orderedDressedNetwork_denote]
      exact (act_comp C D.finalLegs _).symm
    _ = _ := congrArg (act C) (D.network_denote h)

theorem SixDressing.marked_finalKernel (f : Form) (D : SixDressing)
    (hD : ∀j,Direction f (D.legs j)) : Direction f D.finalKernel := by
  have hk : D.finalKernel=(D.legs (D.finalOrder.symm 0)).transpose*
      (Matrix.of Q0)*(D.legs (D.finalOrder.symm 1)) := by
    ext a b
    simp [SixDressing.finalKernel,OctahedralSeparator.pairKernel,Kernel.mul,Kernel.transpose,
      Matrix.mul_apply]
  rw [hk]
  apply OctahedralSeparator.Direction.mul _ (hD _)
  apply OctahedralSeparator.Direction.mul (marked_direction_transpose f (hD _))
  simpa [OctahedralSeparator.complexMatrix_q,quaternionBasis] using OctahedralSeparator.direction_identity f

theorem SixDressing.correctedNetwork_resources (f : Form) (D : SixDressing)
    (hD : ∀j,Direction f (D.legs j)) (C : Legs) (hC : ∀j,Direction f (C j))
    (h : Signature ℂ 6) :
    ∀v,(⟨(D.correctedNetwork C h).shape.arity v,(D.correctedNetwork C h).vertex v⟩ : AnySignature ℂ) ∈
      OctahedralSeparator.markedResources f h := by
  have hp := OctahedralSeparator.pairVertex_available (D.marked_finalKernel f hD)
  have hl (j : Fin 4) := OctahedralSeparator.legVertex_available
    (OctahedralSeparator.Direction.mul (hC j) (hD (D.finalOrder.symm j.succ.succ)))
  intro v
  fin_cases v
  · exact Or.inl (by congr 1; exact OctahedralSeparator.Native.orderedDressedNetwork_ancestor _ _ _ _)
  · exact Or.inr ⟨_,rfl,hp⟩
  · exact Or.inr ⟨_,rfl,hl 0⟩
  · exact Or.inr ⟨_,rfl,hl 1⟩
  · exact Or.inr ⟨_,rfl,hl 2⟩
  · exact Or.inr ⟨_,rfl,hl 3⟩

/-- Full current-coordinate geometric/physical conclusion of A.24 for O′.
No H or inverse-H matrix occurs as a graph resource. -/
theorem prime_deficient_output (h : Signature ℂ 6)
    (hc : ∀i,MarkedCone 1 (actualMap h (markedRepresentative 1 i)))
    (hm : MixedCards (actualMap h) (markedRepresentative 1))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    ∃p : Fin 6,∃N : Network ℂ 4,
      Module.finrank ℂ (actualMap h).range=2 ∧ N.denote=PlatonicDeficient.primeOutput p ∧
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈OctahedralSeparator.markedResources 1 h) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.shape.vertices=6 ∧ N.shape.edges=6 ∧
      ∀r : Fin 3,(flatten r (PlatonicDeficient.primeOutput p)).rank=3 := by
  obtain ⟨p,D,L,hL,he,h2⟩ := marked_deficient_normalization 1 h hc hm hr
  let E := currentDressing 1 D L
  let C : Legs := fun j => OctahedralSeparator.complexMatrix (OctahedralSeparator.corrections 1 j)
  refine ⟨p,E.correctedNetwork C h,h2,?_,
    E.correctedNetwork_resources 1 (currentDressing_directions 1 D L hL) C
      (PlatonicDeficient.prime_legs_available) h,(fun _ => rfl),rfl,rfl,
    PlatonicDeficient.primeOutput_rank_three p⟩
  rw [SixDressing.correctedNetwork_denote,he,PlatonicDeficient.primeOutput_actual]
  rfl

/-- The graph is re-labelled by the recorded actual representatives and their
nonzero product scale, preserving the original finite retained family. -/
theorem prime_deficient_actual_graph {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
    (A : ActualKernelLift Λ D)
    (hcomplete : CompleteKernelRepresentatives {K | Direction 1 K} D)
    (S : SignatureFamily ℂ) (h : Signature ℂ 6)
    (hh : (⟨6,h⟩ : AnySignature ℂ)∈S)
    (hb : ∀K : D,(⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ)∈S)
    (hc : ∀i,MarkedCone 1 (actualMap h (markedRepresentative 1 i)))
    (hm : MixedCards (actualMap h) (markedRepresentative 1))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    ∃p : Fin 6,∃N : Network ℂ 4,∃c : ℂ,c≠0 ∧ N.denote=c • PlatonicDeficient.primeOutput p ∧
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈S) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.shape.vertices=6 ∧ N.shape.edges=6 ∧
      ∀r : Fin 3,(flatten r (PlatonicDeficient.primeOutput p)).rank=3 := by
  obtain ⟨p,N,_,he,hv,hedge,hverts,hedges,hranks⟩ := prime_deficient_output h hc hm hr
  obtain ⟨R⟩ := actualize_network A {K | Direction 1 K} (markedMatrixFamily 1)
    (OctahedralSeparator.direction_X 1) hcomplete S h hh hb N hv
  refine ⟨p,R.network,R.scale,R.scale_ne_zero,?_,R.retained_vertices,hedge,hverts,hedges,hranks⟩
  rw [R.denote,he]

end
end Holant.Platonic.RankDeficientLocalization.Normalization
