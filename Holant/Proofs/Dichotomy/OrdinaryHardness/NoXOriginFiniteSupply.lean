import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginSevenFacePorts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginParallelFace
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalEvenCharacter
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiOppositeCap
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedSource

/-! Genuine origin-supported rank-two/three suppliers. The no-bad alternative
forces exact pair identities; every residual parity alternative is discharged
by an actual original-label even block or the literal opposite anti cap. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginFiniteSupply
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
open OrdinaryNegativeSignedPortsCore (Port word)
namespace U
export OrdinaryNegativeXUniversalResource (EvenBad)
end U
namespace S
export NoXWeightedSignedSource (evenBlock signature ambient_value)
end S
namespace W
export NoXWeightedSignedPorts (table weight)
end W
namespace P
export NoXOriginPorts (two_positive seven_positive two_even seven_even_or_odd)
export NoXOriginSevenFacePorts (ports word_code even_zero odd_one positive_zero)
end P
namespace R2
export OrdinaryNegativeRankTwoPorts (port word_code)
end R2
namespace R3
export OrdinaryNegativeSparseRankThreePorts (port word_code)
end R3
namespace A
export OrdinaryNegativeSparseMixingAlpha (codeThree codeSeven codeThree_affine codeSeven_affine)
end A
namespace C
export NoXOriginPairConditions (negative_even fourth_equal)
end C
namespace O
export NoXWeightedAntiOppositeCap (embedding evenBad_of_affine_compressed)
end O
namespace Sep
export NoXSeparateSignedSource (resource ambient_value)
end Sep
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
local instance : Algebra ℚ K := K.algebra'
variable (H : (i : Fin s)→Signature K (b i.val)) (j antiLabel p0 p1 : Fin s)
variable (v w : K)
variable (ha_lit : (⟨b antiLabel.val,H antiLabel⟩ : AnySignature K)=⟨2,NoXWeightedAntiSigned.anti v w⟩)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin true⟩)
variable (hv : v≠0) (hw : w≠0) (fourth : (v : AlgebraicComplex)^4= -((w : AlgebraicComplex)^4))

def labels : Fin 4→Fin s := ![j,antiLabel,p0,p1]

include ha_lit h0 h1 in
theorem literal (i : Fin 4) :
    (⟨b (labels j antiLabel p0 p1 i).val,H (labels j antiLabel p0 p1 i)⟩ : AnySignature K)=
      ⟨OrdinaryNegativeSignedPortsCore.arity (b j.val) i.val,W.table (H j) v w i⟩ := by
  fin_cases i
  · rfl
  · exact ha_lit
  · exact h0
  · exact h1

variable (atOrigin : H j (origin (b j.val))≠0)
variable (square : Affine (fun z=>(H j z : AlgebraicComplex)^2))
variable (bad : ¬LocalAffine (fun z=>(H j z : AlgebraicComplex)))

include hv hw fourth ha_lit h0 h1 atOrigin square bad in
theorem two (D : SystematicSupport (fun z=>(H j z : AlgebraicComplex)) 2) : U.EvenBad H := by
  by_contra noBad
  have base : (H j (origin (b j.val)) : AlgebraicComplex)≠0 := fun h=>atOrigin (Subtype.ext h)
  have pairs (a c : Word 2) : Even (NoXWeightedRankOneCore.negativeCount (D.encode a) (D.encode c)) :=
    C.negative_even H j antiLabel p0 p1 v w ha_lit h0 h1 hv hw fourth noBad _ _
      (fun h=>D.supported a (congrArg (fun z : K=>(z : AlgebraicComplex)) h))
      (fun h=>D.supported c (congrArg (fun z : K=>(z : AlgebraicComplex)) h)) atOrigin
  exact noBad (NoXLocalEvenCharacter.evenBad H j (labels j antiLabel p0 p1) v w
    (literal H j antiLabel p0 p1 v w ha_lit h0 h1) hv hw fourth D (R2.port D)
    A.codeThree A.codeThree_affine (R2.word_code D) (P.two_even D base pairs) square bad)

include hv hw fourth ha_lit h0 h1 atOrigin square bad in
theorem three (D : SystematicSupport (fun z=>(H j z : AlgebraicComplex)) 3) : U.EvenBad H := by
  by_contra noBad
  have base : (H j (origin (b j.val)) : AlgebraicComplex)≠0 := fun h=>atOrigin (Subtype.ext h)
  have supported (x : Word 3) : H j (D.encode x)≠0 :=
    fun h=>D.supported x (congrArg (fun z : K=>(z : AlgebraicComplex)) h)
  have pairs (a c : Word 3) : Even (NoXWeightedRankOneCore.negativeCount (D.encode a) (D.encode c)) :=
    C.negative_even H j antiLabel p0 p1 v w ha_lit h0 h1 hv hw fourth noBad _ _
      (supported a) (supported c) atOrigin
  rcases P.seven_even_or_odd D base pairs with even|odd
  · exact noBad (NoXLocalEvenCharacter.evenBad H j (labels j antiLabel p0 p1) v w
      (literal H j antiLabel p0 p1 v w ha_lit h0 h1) hv hw fourth D (R3.port D)
      A.codeSeven A.codeSeven_affine (R3.word_code D) even square bad)
  · have positive := P.seven_positive D base
    let ps0 := P.ports (R3.port D) false
    let ps1 := P.ports (R3.port D) true
    have even0 := P.even_zero (R3.port D) positive odd
    have odd1 := P.odd_one (R3.port D) positive odd
    let block := S.evenBlock H (labels j antiLabel p0 p1) (H j) v w
      (literal H j antiLabel p0 p1 v w ha_lit h0 h1) ps0 even0
    have blockAffine : Affine (fun z=>(block.signature H z : AlgebraicComplex)) := by
      by_contra failure
      exact noBad ⟨3,block,failure⟩
    have affine0 : Affine (NoXOriginParallelFace.face D.reduced false) := by
      have pull:=blockAffine.precompose A.codeThree A.codeThree_affine
      change Affine (fun x=>(S.signature H (labels j antiLabel p0 p1) (H j) v w
        (literal H j antiLabel p0 p1 v w ha_lit h0 h1) ps0 (A.codeThree x) : AlgebraicComplex)) at pull
      convert pull using 1
      funext x
      rw [S.ambient_value,NoXUnsignedRows.weight_one _ _ _ (P.positive_zero (R3.port D)),one_mul]
      rw [P.word_code _ positive,R3.word_code]
      rfl
    have reducedFourth (x y : Word 3) : D.reduced x^4=D.reduced y^4 :=
      C.fourth_equal H j antiLabel p0 p1 v w ha_lit h0 h1 hv hw fourth noBad _ _
        (supported x) (supported y) atOrigin
    have affine1 := NoXOriginParallelFace.affine_parallel D.reduced D.supported
      (square.precompose D.encode D.affine) reducedFourth affine0
    let resource := Sep.resource H j p0 p1 h0 h1 ps1 odd1
    have compressed (x : Word 2) : resource.ambient H (O.embedding .three x)=
        NoXOriginParallelFace.face D.reduced true x := by
      change resource.ambient H (Fin.addCases (A.codeThree x) (fun q=>!(A.codeThree x q)))=_
      rw [Sep.ambient_value,P.word_code _ positive,R3.word_code]
      rfl
    apply noBad
    apply O.evenBad_of_affine_compressed .three H antiLabel v w ha_lit resource hv hw fourth
    · simpa only [compressed] using affine1
    · intro x
      rw [compressed]
      exact D.supported _

include atOrigin in
theorem affine_of_local (hl : LocalAffine (fun z=>(H j z : AlgebraicComplex))) :
    Affine (fun z=>(H j z : AlgebraicComplex)) := by
  have ha:=hl (origin (b j.val)) (fun h=>atOrigin (Subtype.ext h))
  have he : localTwist (origin (b j.val)) (fun z=>(H j z : AlgebraicComplex))=
      (fun z=>(H j z : AlgebraicComplex)) := by
    funext x
    simp only [localTwist_apply,AffinePhase.origin,Bool.false_and,Bool.false_eq_true,
      ite_false,Finset.prod_const_one,one_mul]
  rwa [he] at ha

include hv hw fourth ha_lit h0 h1 atOrigin square in
theorem bounded {r : ℕ} (D : SystematicSupport (fun z=>(H j z : AlgebraicComplex)) r)
    (lower : 1≤r) (upper : r≤3) (nonAffine : ¬Affine (fun z=>(H j z : AlgebraicComplex))) : U.EvenBad H := by
  have nonLocal : ¬LocalAffine (fun z=>(H j z : AlgebraicComplex)) :=
    fun h=>nonAffine (affine_of_local H j atOrigin h)
  have cases : r=1 ∨ r=2 ∨ r=3 := by omega
  rcases cases with rfl|rfl|rfl
  · exact NoXLocalRankOneSource.evenBad_of_rank_one H j antiLabel p0 p1 v w ha_lit h0 h1
      hv hw D square nonLocal fourth
  · exact two H j antiLabel p0 p1 v w ha_lit h0 h1 hv hw fourth atOrigin square nonLocal D
  · exact three H j antiLabel p0 p1 v w ha_lit h0 h1 hv hw fourth atOrigin square nonLocal D


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginFiniteSupply
end
