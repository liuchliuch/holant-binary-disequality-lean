import Holant.Platonic.RankDeficientLocalization.Normalization.StandardOutputs
import Holant.NetworkAlgebra
import Holant.Platonic.RainbowLocalization.PhysicalCanonicalDeck
import Holant.Certificates.RainbowOrbit.MarkedFamily

/-! Replace all local projective group directions by the stored actual binary
representatives.  Every original scalar is recorded once at its graph vertex. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.RainbowLocalization.Physical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical

abbrev NativeBinary := OctahedralSeparator.Native.Binary
abbrev nativeTransfer := OctahedralSeparator.nativeTransfer
abbrev nativePair (B : NativeBinary) : Mat := Holant.Certificates.MatchingContractionClosure.nativePair B
abbrev binarySignature (B : NativeBinary) : Signature ℂ 2 := Holant.Certificates.MatchingContractionClosure.binarySignature B

def directionResources (G : Set Mat) (h : Signature ℂ 6) : SignatureFamily ℂ :=
  {t | t=⟨6,h⟩ ∨ ∃B : NativeBinary,t=⟨2,binarySignature B⟩ ∧ nativeTransfer B∈G}

theorem nativePair_involution (B : NativeBinary) : nativePair (nativePair B)=B := by
  ext a b
  simp only [Holant.Certificates.MatchingContractionClosure.nativePair_apply,Bool.not_not]

theorem nativePair_transfer (B : NativeBinary) : nativePair B=(Matrix.of X)*nativeTransfer B := by
  ext a b
  cases a <;> cases b <;>
    simp [Holant.Certificates.MatchingContractionClosure.nativePair_apply,nativeTransfer,
      OctahedralSeparator.nativeTransfer,Matrix.mul_apply,Kernel.mul,X,Signature.disequality]

theorem actual_binary_scale {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
    (A : ActualKernelLift Λ D) (G : Set Mat) (hG : MatrixFamily G) (hX : (Matrix.of X)∈G)
    (hcomplete : CompleteKernelRepresentatives G D) (B : NativeBinary)
    (hB : nativeTransfer B∈G) :
    ∃K : D,∃c : ℂ,c≠0 ∧ A.binary K=c • B := by
  have hK : nativePair B∈G := by rw [nativePair_transfer]; exact hG.mul hX hB
  obtain ⟨K,hK,c,hc,he⟩ := hcomplete _ hK
  let K' : D := ⟨K,hK⟩
  have hrep : B=c • nativePair K := by
    have hh := congrArg nativePair he
    rw [nativePair_involution] at hh
    exact hh.trans (nativePair_smul c K)
  refine ⟨K',A.scalar K'/c,div_ne_zero (A.scalar_ne_zero K') hc,?_⟩
  rw [A.normalization,hrep,smul_smul,div_mul_cancel₀ _ hc]

/-- This data changes only vertex coefficients on an existing ordinary graph.
The original six-port label keeps scale1; every binary keeps its actual label. -/
structure Actualization {n : ℕ} (N : Network ℂ n) (S : SignatureFamily ℂ) where
  scales : Fin N.shape.vertices → ℂ
  scales_ne_zero : ∀v,scales v≠0
  vertex_mem : ∀v,(⟨N.shape.arity v,scales v • N.vertex v⟩ : AnySignature ℂ) ∈ S
  ancestor_scale : ∀v,N.shape.arity v=6 → scales v=1

def Actualization.network {n : ℕ} {N : Network ℂ n} {S : SignatureFamily ℂ}
    (A : Actualization N S) : Network ℂ n := N.scaleVertices A.scales

def Actualization.scale {n : ℕ} {N : Network ℂ n} {S : SignatureFamily ℂ}
    (A : Actualization N S) : ℂ := ∏v,A.scales v

theorem Actualization.scale_ne_zero {n : ℕ} {N : Network ℂ n} {S : SignatureFamily ℂ}
    (A : Actualization N S) : A.scale≠0 := Finset.prod_ne_zero_iff.mpr (fun v _ => A.scales_ne_zero v)

theorem Actualization.denote {n : ℕ} {N : Network ℂ n} {S : SignatureFamily ℂ}
    (A : Actualization N S) : A.network.denote=A.scale • N.denote := by
  funext x
  exact N.denote_scaleVertices A.scales x

theorem Actualization.retained_vertices {n : ℕ} {N : Network ℂ n} {S : SignatureFamily ℂ}
    (A : Actualization N S) :
    ∀v,(⟨A.network.shape.arity v,A.network.vertex v⟩ : AnySignature ℂ) ∈ S := A.vertex_mem

theorem actualize_network {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
    (A : ActualKernelLift Λ D) (G : Set Mat) (hG : MatrixFamily G) (hX : (Matrix.of X)∈G)
    (hcomplete : CompleteKernelRepresentatives G D) (S : SignatureFamily ℂ)
    (h : Signature ℂ 6) (hh : (⟨6,h⟩ : AnySignature ℂ) ∈ S)
    (hb : ∀K : D,(⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ) ∈ S)
    {n : ℕ} (N : Network ℂ n)
    (hN : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ) ∈ directionResources G h) :
    Nonempty (Actualization N S) := by
  have hs (t : AnySignature ℂ) (ht : t∈directionResources G h) :
      ∃c : ℂ,c≠0 ∧ (⟨t.1,c • t.2⟩ : AnySignature ℂ)∈S ∧ (t.1=6 → c=1) := by
    rcases ht with rfl|⟨B,rfl,hB⟩
    · exact ⟨1,one_ne_zero,by simpa using hh,fun _ => rfl⟩
    · obtain ⟨K,c,hc,he⟩ := actual_binary_scale A G hG hX hcomplete B hB
      refine ⟨c,hc,?_,by norm_num⟩
      have hsig : c • binarySignature B=binarySignature (A.binary K) := by
        rw [he]
        rfl
      rw [hsig]
      exact hb K
  choose c hc hmem hone using fun v => hs _ (hN v)
  exact ⟨⟨c,hc,hmem,hone⟩⟩

/-- Standard A.24 output, now with literal retained labels and the complete
nonzero scalar from the actual representative choices. -/
theorem standard_deficient_actual_graph {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
    (A : ActualKernelLift Λ D) (g : PlatonicModel)
    (hcomplete : CompleteKernelRepresentatives {K | groupDirection g K} D)
    (S : SignatureFamily ℂ) (h : Signature ℂ 6)
    (hh : (⟨6,h⟩ : AnySignature ℂ)∈S)
    (hb : ∀K : D,(⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ)∈S)
    (hc : ∀i,matchingCone g (actualMap h (representative g i)))
    (hm : MixedCards (actualMap h) (representative g))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    ∃p : Fin 6,∃N : Network ℂ 4,∃c : ℂ,c≠0 ∧ N.denote=c • PlatonicDeficient.output p ∧
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈S) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.shape.vertices=6 ∧ N.shape.edges=6 ∧
      (PlatonicDeficient.support (PlatonicDeficient.output p)).card=10 ∧
      ∀r : Fin 3,(flatten r (PlatonicDeficient.output p)).rank=3 := by
  obtain ⟨p,E,_,he,hv,hedge,_,hverts,hedges,hsupport,hranks⟩ := standard_deficient_output g h hc hm hr
  obtain ⟨R⟩ := actualize_network A {K | groupDirection g K} (standardMatrixFamily g)
    (X_direction g) hcomplete S h hh hb (E.network h) hv
  refine ⟨p,R.network,R.scale,R.scale_ne_zero,?_,R.retained_vertices,hedge,hverts,hedges,hsupport,hranks⟩
  rw [R.denote,he]

end
end Holant.Platonic.RankDeficientLocalization.Normalization
