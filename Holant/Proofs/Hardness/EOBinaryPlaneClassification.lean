import Holant.Proofs.Hardness.EOBinaryPlaneAffine
import Holant.Proofs.Hardness.EOBinaryPlaneProduct
import Holant.Proofs.Hardness.EOBinaryPlaneTract
import Holant.Proofs.Hardness.EOQuaternarySparseTract

/-! Exact coefficient classification of the remaining binary plane.
Full-support product means determinant zero. Full-support affine means common
fourth powers and a signed cross-product identity. Three-supported binaries
fail both literal classes by a missing ternary-XOR word. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open scoped BigOperators
namespace P
export EOQuaternarySparseTract (binary_of_shape support)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000


private theorem xor_missing_ff :
    xor3 (![false,true] : Fin 2→Bool) ![true,false] ![true,true]=![false,false] := by decide
private theorem xor_missing_ft :
    xor3 (![false,false] : Fin 2→Bool) ![true,false] ![true,true]=![false,true] := by decide
private theorem xor_missing_tf :
    xor3 (![false,false] : Fin 2→Bool) ![false,true] ![true,true]=![true,false] := by decide
private theorem xor_missing_tt :
    xor3 (![false,false] : Fin 2→Bool) ![false,true] ![true,false]=![true,true] := by decide

theorem three_obstruction (f : Signature AlgebraicComplex 2) (hf : (P.support f).card=3) :
    ∃a b c,f a≠0 ∧ f b≠0 ∧ f c≠0 ∧ f (xor3 a b c)=0 := by
  classical
  have hu : (Finset.univ : Finset (Fin 2→Bool))=
      {![false,false],![false,true],![true,false],![true,true]} := by decide
  by_cases h0 : f ![false,false]=0 <;> by_cases h1 : f ![false,true]=0 <;>
    by_cases h2 : f ![true,false]=0 <;> by_cases h3 : f ![true,true]=0
  all_goals simp [P.support,hu,Finset.filter_insert,Finset.filter_singleton,h0,h1,h2,h3] at hf
  all_goals first
    | exact ⟨![false,true],![true,false],![true,true],h1,h2,h3,by rwa [xor_missing_ff]⟩
    | exact ⟨![false,false],![true,false],![true,true],h0,h2,h3,by rwa [xor_missing_ft]⟩
    | exact ⟨![false,false],![false,true],![true,true],h0,h1,h3,by rwa [xor_missing_tf]⟩
    | exact ⟨![false,false],![false,true],![true,false],h0,h1,h2,by rwa [xor_missing_tt]⟩

theorem three_not_affine (f : Signature AlgebraicComplex 2) (hf : (P.support f).card=3) : ¬Affine f := by
  intro h
  obtain ⟨a,b,c,ha,hb,hc,hz⟩ := three_obstruction f hf
  exact affine_support_xor3 h a b c ha hb hc hz

theorem three_not_product (f : Signature AlgebraicComplex 2) (hf : (P.support f).card=3) : ¬Product f := by
  intro h
  obtain ⟨a,b,c,ha,hb,hc,hz⟩ := three_obstruction f hf
  exact product_support_xor3 h a b c ha hb hc hz

theorem three_not_tract (f : Signature AlgebraicComplex 2) (hf : (P.support f).card=3) :
    ¬EOTract {⟨4,EOBinaryPlaneCore.lift f⟩} := by
  rw [EOBinaryPlaneTract.lift_tract_iff]
  exact not_or.mpr ⟨three_not_affine f hf,three_not_product f hf⟩

theorem full_lift_tract_iff (f : Signature AlgebraicComplex 2) (hf : Full f) :
    EOTract {⟨4,EOBinaryPlaneCore.lift f⟩} ↔ (CommonFourth f ∧ SignedCross f) ∨ Cross f := by
  rw [EOBinaryPlaneTract.lift_tract_iff,full_affine_iff f hf,full_product_iff f hf]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification
