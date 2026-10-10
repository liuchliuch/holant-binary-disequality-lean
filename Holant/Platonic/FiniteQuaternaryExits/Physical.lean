import Holant.Platonic.FiniteQuaternaryExits.Nonzero
import Holant.Platonic.RankDeficientLocalization.Normalization.ActualRepresentatives
import Holant.OpenNetworkComposition.ProjectiveSubstitution
import Holant.Certificates.OppositeIcosahedral.PhysicalDictionary

namespace Holant.Platonic.FiniteQuaternaryExits
open Holant Holant.Certificates Holant.Certificates.PlatonicQuaternaryExits
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Platonic.RainbowLocalization.Physical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SourceCase

theorem group_mul (s : PlatonicQuaternaryExits.SourceCase)
    {U V : Matrix Bool Bool ℂ} (hU : s.group U) (hV : s.group V) : s.group (U*V) := by
  cases s with
  | tetrahedralDeficient p => exact RainbowOrbit.groupDirection_mul _ hU hV
  | tetrahedralReverse p => exact RainbowOrbit.groupDirection_mul _ hU hV
  | octahedralDeficient f p => exact OctahedralSeparator.Direction.mul hU hV
  | mixedDeficient f p => exact OctahedralSeparator.Direction.mul hU hV
  | octahedralFrame f i p => exact OctahedralSeparator.Direction.mul hU hV
  | icosahedralDeficient o p =>
    cases o
    · exact RainbowOrbit.groupDirection_mul _ hU hV
    · exact OppositeIcosahedral.Direction.mul hU hV
  | icosahedralFrame o p =>
    cases o
    · exact RainbowOrbit.groupDirection_mul _ hU hV
    · exact OppositeIcosahedral.Direction.mul hU hV

theorem group_X (s : PlatonicQuaternaryExits.SourceCase) : s.group (Matrix.of X) := by
  cases s with
  | tetrahedralDeficient p => exact X_direction .tetrahedral
  | tetrahedralReverse p => exact X_direction .tetrahedral
  | octahedralDeficient f p => exact OctahedralSeparator.direction_X _
  | mixedDeficient f p => exact OctahedralSeparator.direction_X _
  | octahedralFrame f i p => exact OctahedralSeparator.direction_X _
  | icosahedralDeficient o p =>
    cases o
    · exact X_direction .icosahedral
    · exact OppositeIcosahedral.direction_X
  | icosahedralFrame o p =>
    cases o
    · exact X_direction .icosahedral
    · exact OppositeIcosahedral.direction_X
end SourceCase

theorem actual_group_binary {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
    (s : PlatonicQuaternaryExits.SourceCase) (A : ActualKernelLift Λ D)
    (hcomplete : CompleteKernelRepresentatives {K | s.group K} D)
    (B : OctahedralSeparator.Native.Binary) (hB : s.group (OctahedralSeparator.nativeTransfer B)) :
    Gadget.RealizesUpTo Λ .disequality (OctahedralSeparator.Native.binarySignature B) := by
  open RankDeficientLocalization.Normalization in
  have hK : s.group (nativePair B) := by
    rw [nativePair_transfer]
    exact SourceCase.group_mul s (SourceCase.group_X s) hB
  obtain ⟨K,hK,c,hc,he⟩ := hcomplete _ hK
  let K' : D := ⟨K,hK⟩
  have hrep : B=c • RankDeficientLocalization.Normalization.nativePair K := by
    have hh := congrArg RankDeficientLocalization.Normalization.nativePair he
    rw [RankDeficientLocalization.Normalization.nativePair_involution] at hh
    exact hh.trans (Holant.Platonic.RainbowLocalization.Physical.nativePair_smul c K)
  let d : ℂ := A.scalar K'/c
  have hd : d≠0 := div_ne_zero (A.scalar_ne_zero K') hc
  have hbin : A.binary K'=d • B := by
    rw [A.normalization,hrep,smul_smul]
    dsimp [d]
    rw [div_mul_cancel₀ _ hc]
  refine ⟨d,hd,?_⟩
  have ha := A.actual K'
  rw [hbin] at ha
  exact ha

theorem bounded_actual {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
    (s : PlatonicQuaternaryExits.SourceCase) (A : ActualKernelLift Λ D)
    (hcomplete : CompleteKernelRepresentatives {K | s.group K} D)
    (hq : Gadget.RealizesUpTo Λ .disequality s.signature)
    {n : ℕ} {t : Signature ℂ n} (h : BoundedRealization s.group s.signature t) :
    Gadget.RealizesUpTo Λ .disequality t := by
  obtain ⟨N,hN,hv,he,_,_⟩ := h
  rw [←hN]
  apply OpenNetworkComposition.realizesUpTo_network Λ N _ he (by norm_num)
  intro v
  have hmem := hv v
  rcases hmem with heq|⟨B,heq,hB⟩
  · have hh := congrArg (fun u : AnySignature ℂ => Gadget.RealizesUpTo Λ .disequality u.2) heq
    exact hh.mpr hq
  · have hh := congrArg (fun u : AnySignature ℂ => Gadget.RealizesUpTo Λ .disequality u.2) heq
    exact hh.mpr (actual_group_binary s A hcomplete B hB)

def ActualExit (Λ : SignatureFamily ℂ) (s : PlatonicQuaternaryExits.SourceCase) : Prop :=
  (∃ t : Signature ℂ 4,BoundedRealization s.group s.signature t ∧
    Gadget.RealizesUpTo Λ .disequality t ∧
    TetrahedralOrientation.EndpointNondegenerateEightVertex t ∧
    ∀r : Fin 3,(flatten r t).rank=2) ∨
  (∃ t : Signature ℂ 4,BoundedRealization s.group s.signature t ∧
    Gadget.RealizesUpTo Λ .disequality t ∧ PureGeneralizedEquality4 t) ∨
  ∃B : Kernel ℂ,BoundedRealization s.group s.signature (OctahedralSeparator.Native.binarySignature B) ∧
    Gadget.RealizesUpTo Λ .disequality
    (OctahedralSeparator.Native.binarySignature B) ∧ Matrix.det (Matrix.of B)≠0 ∧
      ¬s.group (OctahedralSeparator.nativeTransfer B)

theorem all_cases_actual_exit {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
    (s : PlatonicQuaternaryExits.SourceCase) (A : ActualKernelLift Λ D)
    (hcomplete : CompleteKernelRepresentatives {K | s.group K} D)
    (hq : Gadget.RealizesUpTo Λ .disequality s.signature) : ActualExit Λ s := by
  rcases all_platonic_quaternary_exits s with ⟨t,ht,hE,hr⟩ | ⟨t,ht,hE⟩ | ⟨B,hB,hd,ho⟩
  · exact Or.inl ⟨t,ht,bounded_actual s A hcomplete hq ht,hE,hr⟩
  · exact Or.inr (Or.inl ⟨t,ht,bounded_actual s A hcomplete hq ht,hE⟩)
  · exact Or.inr (Or.inr ⟨B,hB,bounded_actual s A hcomplete hq hB,hd,ho⟩)
end
end Holant.Platonic.FiniteQuaternaryExits
